package obfuscator

import (
	"context"
	"encoding/base64"
	"fmt"
	"math/rand"
	"strconv"
	"strings"
	"time"

	"github.com/LazarenkoA/1c-language-parser/ast"
	"github.com/knetic/govaluate"
	"github.com/pkg/errors"
)

// Config содержит настройки обфускатора
type Config struct {
	// RepExpByTernary заменять выражение тернарными операторами
	RepExpByTernary bool
	// RepLoopByGoto заменять циклы на Перейти
	RepLoopByGoto bool
	// RepExpByEval прятать выражения в Выполнить() Вычислить()
	RepExpByEval bool
	// HideString прятать строки
	HideString bool
	// ChangeConditions изменять условия
	ChangeConditions bool
	// AppendGarbage добавлять мусора
	AppendGarbage bool
}

type Obfuscator struct {
	ctx                  context.Context
	conf                 Config
	a                    *ast.AstNode
	trueCondition        chan string
	falseCondition       chan string
	decodeStringFuncName map[string]string
	// ИЗМЕНЕНИЕ: Временное хранилище для сгенерированных функций
	generatedFuncs []ast.Statement
	// ИЗМЕНЕНИЕ: Добавляем собственный экземпляр rand для предсказуемости/непредсказуемости
	r *rand.Rand
}

// init инициализирует пакет. В данном случае не используется, но оставлено для структуры.
func init() {
}

// NewObfuscatory создает новый экземпляр обфускатора
func NewObfuscatory(ctx context.Context, conf Config) *Obfuscator {
	// ИЗМЕНЕНИЕ: Инициализируем генератор случайных чисел.
	// Используем текущее время для получения разных результатов при каждом запуске.
	source := rand.NewSource(time.Now().UnixNano())
	randomizer := rand.New(source)

	c := &Obfuscator{
		ctx:                  ctx,
		conf:                 conf,
		trueCondition:        make(chan string, 10),
		falseCondition:       make(chan string, 10),
		decodeStringFuncName: make(map[string]string),
		// ИЗМЕНЕНИЕ: Инициализируем срез для сгенерированных функций
		generatedFuncs: make([]ast.Statement, 0),
		r:              randomizer,
	}

	c.genCondition()
	return c
}

// Obfuscate выполняет обфускацию переданного кода
func (c *Obfuscator) Obfuscate(code string) (string, error) {
	c.a = ast.NewAST(code)
	if err := c.a.Parse(); err != nil {
		return "", err
	}

	if len(c.a.ModuleStatement.Body) == 0 {
		return code, nil
	}

	// Очищаем сгенерированные функции от предыдущих запусков, если обфускатор используется повторно
	c.generatedFuncs = make([]ast.Statement, 0)

	c.a.ModuleStatement.Walk(func(currentFP *ast.FunctionOrProcedure, statement *ast.Statement) {
		c.walkStep(currentFP, nil, statement)
	})

	// ИЗМЕНЕНИЕ: Добавляем все сгенерированные функции в AST после того, как обход завершен
	if len(c.generatedFuncs) > 0 {
		c.a.ModuleStatement.Body = append(c.a.ModuleStatement.Body, c.generatedFuncs...)
	}

	result := c.a.Print(ast.PrintConf{OneLine: true, Margin: 1})
	return result, nil
}

func (c *Obfuscator) walkStep(currentFP *ast.FunctionOrProcedure, parent, item *ast.Statement) {
	if currentFP == nil {
		// Это может произойти, если код находится вне процедур/функций.
		// В 1С это возможно для исполняемого кода модуля.
		// Вместо вывода в консоль, можно решить, как обрабатывать такие случаи.
		// Пока что пропускаем.
		return
	}

	key := float64(c.random(10, 100))

	switch v := (*item).(type) {
	case *ast.IfStatement:
		c.walkStep(currentFP, item, &v.Expression)

		v.Expression = c.appendConditions(v.Expression)
		if c.conf.ChangeConditions {
			c.appendIfElseBlock(&v.IfElseBlock, int(c.random(0, 5)))
			c.appendGarbage(&v.ElseBlock)
			c.appendGarbage(&v.TrueBlock)
		}

	case *ast.FunctionOrProcedure:
		c.appendGarbage(&v.Body)

	case ast.MethodStatement:
		for i, param := range v.Param {
			switch casted := param.(type) {
			case *ast.ExpStatement, ast.MethodStatement:
				c.walkStep(currentFP, item, &casted)
			case string:
				if c.conf.HideString {
					v.Param[i] = ast.MethodStatement{
						Name:  c.decodeStringFunc(currentFP.Directive),
						Param: []ast.Statement{c.obfuscateString(casted, int32(key)), c.hideValue(key, 4)},
					}
				}
			}
		}

		if c.conf.RepExpByEval && parent == nil && c.random(0, 2) == 1 {
			str := c.a.PrintStatementWithConf(v, ast.PrintConf{})
			if len(str) > 0 && str[len(str)-1] == ';' {
				str = str[:len(str)-1]
			}

			*item = ast.MethodStatement{
				Name: "Выполнить",
				Param: []ast.Statement{
					ast.MethodStatement{
						Name:  c.decodeStringFunc(currentFP.Directive),
						Param: []ast.Statement{c.obfuscateString(str, int32(key)), c.hideValue(key, 4)},
					},
				},
			}
		}

	case *ast.ReturnStatement:
		if str, ok := v.Param.(string); ok && c.conf.HideString {
			v.Param = ast.MethodStatement{
				Name:  c.decodeStringFunc(currentFP.Directive),
				Param: []ast.Statement{c.obfuscateString(str, int32(key)), c.hideValue(key, 4)},
			}
		}
	case *ast.ExpStatement:
		c.obfuscateExpStatement(currentFP, (*interface{})(item))

		if _, ok := v.Left.(ast.VarStatement); ok && c.conf.RepExpByEval {
			switch v.Right.(type) {
			case ast.MethodStatement, ast.CallChainStatement, ast.NewObjectStatement:
				str := c.a.PrintStatementWithConf(v.Right, ast.PrintConf{})
				if len(str) > 0 && str[len(str)-1] == ';' {
					str = str[:len(str)-1]
				}

				v.Right = ast.MethodStatement{
					Name: "Вычислить",
					Param: []ast.Statement{ast.MethodStatement{
						Name:  c.decodeStringFunc(currentFP.Directive),
						Param: []ast.Statement{c.obfuscateString(str, int32(key)), c.hideValue(key, 4)},
					}},
				}
			default:
				v.Right = c.hideValue(v.Right, 4)
			}
		}
	case ast.CallChainStatement:
		c.walkStep(currentFP, item, &v.Unit)

		if c.conf.RepExpByEval && parent == nil && c.random(0, 2) == 1 {
			str := c.a.PrintStatementWithConf(v, ast.PrintConf{})
			if len(str) > 0 && str[len(str)-1] == ';' {
				str = str[:len(str)-1]
			}

			*item = ast.MethodStatement{
				Name: "Выполнить",
				Param: []ast.Statement{
					ast.MethodStatement{
						Name:  c.decodeStringFunc(currentFP.Directive),
						Param: []ast.Statement{c.obfuscateString(str, int32(key)), c.hideValue(key, 4)},
					},
				},
			}
		}
	case *ast.LoopStatement:
		c.replaceLoopToGoto(&currentFP.Body, v, false)
	case ast.ThrowStatement:
		switch casted := v.Param.(type) {
		case *ast.ExpStatement, ast.MethodStatement:
			c.walkStep(currentFP, item, &casted)
		}
	}
}

func (c *Obfuscator) obfuscateExpStatement(currentPF *ast.FunctionOrProcedure, part *interface{}) {
	key := float64(c.random(10, 100))

	switch r := (*part).(type) {
	case *ast.ExpStatement:
		c.obfuscateExpStatement(currentPF, &r.Right)
		c.obfuscateExpStatement(currentPF, &r.Left)

		if c.conf.RepExpByTernary {
			r.Right = c.hideValue(r.Right, 4)
		}
	case string:
		if c.conf.HideString {
			*part = ast.MethodStatement{
				Name:  c.decodeStringFunc(currentPF.Directive),
				Param: []ast.Statement{c.obfuscateString(r, int32(key)), c.hideValue(key, 4)},
			}
		}
		return
	case ast.ReturnStatement:
		if str, ok := r.Param.(string); ok && c.conf.HideString {
			r.Param = ast.MethodStatement{
				Name:  c.decodeStringFunc(currentPF.Directive),
				Param: []ast.Statement{c.obfuscateString(str, int32(key)), c.hideValue(key, 4)},
			}
		}
	case ast.IParams:
		for i, param := range r.Params() {
			if str, ok := param.(string); ok && c.conf.HideString {
				r.Params()[i] = ast.MethodStatement{
					Name:  c.decodeStringFunc(currentPF.Directive),
					Param: []ast.Statement{c.obfuscateString(str, int32(key)), c.hideValue(key, 4)},
				}
			}
		}
	}
}

func (c *Obfuscator) decodeStringFunc(directive string) string {
	if name, ok := c.decodeStringFuncName[directive]; ok {
		return name
	}

	name := c.newDecodeStringFunc(directive)
	c.decodeStringFuncName[directive] = name
	return name
}

func (c *Obfuscator) hideValue(val interface{}, complexity int) ast.Statement {
	switch val.(type) {
	case string, bool, float64, int, time.Time, *ast.ExpStatement, ast.MethodStatement:
		return c.newTernary(val, int(c.random(2, int64(complexity))), int(c.random(0, int64(complexity-1))))
	default:
		return val
	}
}

func (c *Obfuscator) appendGarbage(body *[]ast.Statement) {
	if !c.conf.AppendGarbage {
		return
	}

	if c.random(0, 2) == 1 {
		*body = append(*body, &ast.ExpStatement{
			Operation: ast.OpEq,
			Left:      ast.VarStatement{Name: c.randomString(20)},
			Right:     c.hideValue(c.randomString(5), 4),
		})
	}
	if c.random(0, 2) == 1 {
		*body = append(*body, &ast.ExpStatement{
			Operation: ast.OpEq,
			Left:      ast.VarStatement{Name: c.randomString(10)},
			Right:     c.hideValue(float64(c.random(-100, 100)), 5),
		})
	}
	if c.random(0, 2) == 1 {
		exp, err := c.convStrExpToExpStatement(<-c.falseCondition)
		if err != nil {
			return // Пропускаем добавление мусора, если не удалось спарсить выражение
		}
		IF := &ast.IfStatement{Expression: exp}

		if c.random(0, 2) == 1 {
			c.appendIfElseBlock(&IF.IfElseBlock, int(c.random(0, 5)))
		}
		if c.random(0, 2) == 1 {
			c.appendGarbage(&IF.ElseBlock)
			c.appendGarbage(&IF.TrueBlock)
		}
		*body = append(*body, IF)
	}
	if c.random(0, 2) == 1 {
		exp, err := c.convStrExpToExpStatement(<-c.falseCondition)
		if err != nil {
			return
		}
		loop := &ast.LoopStatement{WhileExpr: exp}
		if c.random(0, 2) == 1 {
			c.appendGarbage(&loop.Body)
		}
		*body = append(*body, loop)
	}
}

func (c *Obfuscator) appendIfElseBlock(ifElseBlock *[]ast.Statement, count int) {
	for i := 0; i < count; i++ {
		exp, err := c.convStrExpToExpStatement(<-c.falseCondition)
		if err != nil {
			continue // Пропускаем
		}
		*ifElseBlock = append(*ifElseBlock, &ast.IfStatement{
			Expression: exp,
		})
	}
}

func (c *Obfuscator) appendConditions(exp ast.Statement) ast.Statement {
	if !c.conf.ChangeConditions {
		return exp
	}
	// Уменьшаем глубину, чтобы не создавать слишком громоздкие конструкции
	return c.helperAppendConditions(exp, 2)
}

func (c *Obfuscator) helperAppendConditions(exp ast.Statement, depth int) ast.Statement {
	if depth == 0 {
		return exp
	}

	trueCondExp, err := c.convStrExpToExpStatement(<-c.trueCondition)
	if err != nil {
		return exp // Возвращаем исходное выражение при ошибке
	}

	newConditions := &ast.ExpStatement{
		Operation: ast.OpAnd,
		Left:      exp,
		Right:     trueCondExp,
	}

	if c.random(0, 2) == 1 {
		// Меняем местами для разнообразия
		newConditions.Left, newConditions.Right = newConditions.Right, newConditions.Left
	}

	return c.helperAppendConditions(newConditions, depth-1)
}

func (c *Obfuscator) newTernary(trueValue interface{}, depth, trueStep int) ast.TernaryStatement {
	if depth < trueStep {
		depth, trueStep = trueStep, depth
	}

	var expression ast.Statement
	var value interface{}

	// Выбираем, будет ли текущее условие истинным или ложным
	if trueStep == 0 {
		exp, err := c.convStrExpToExpStatement(<-c.trueCondition)
		if err != nil {
			// В случае ошибки создаем простое "истинное" выражение
			expression = ast.NewBool(true)
		} else {
			expression = exp
		}
		value = trueValue
	} else {
		exp, err := c.convStrExpToExpStatement(<-c.falseCondition)
		if err != nil {
			// В случае ошибки создаем простое "ложное" выражение
			expression = ast.NewBool(false)
		} else {
			expression = exp
		}
		value = c.fakeValue(trueValue)
	}

	// Базовый случай рекурсии
	if depth == 0 {
		return ast.TernaryStatement{
			Expression: expression,
			TrueBlock:  value,
			ElseBlock:  c.fakeValue(trueValue),
		}
	}

	// Рекурсивный шаг
	return ast.TernaryStatement{
		Expression: expression,
		TrueBlock:  value,
		ElseBlock:  c.newTernary(trueValue, depth-1, trueStep-1),
	}
}

func (c *Obfuscator) fakeValue(value interface{}) interface{} {
	switch value.(type) {
	case float64:
		return float64(c.random(0, 1000))
	case int:
		return float64(c.random(0, 1000))
	case string:
		return c.randomString(10)
	case *ast.ExpStatement:
		exp, err := c.convStrExpToExpStatement(<-c.falseCondition)
		if err != nil {
			return ast.NewString("error")
		}
		return exp
	case ast.MethodStatement:
		return c.fakeMethods()
	default:
		return value
	}
}

func (c *Obfuscator) fakeMethods() ast.MethodStatement {
	pool := []ast.MethodStatement{
		{Name: "XMLСтрока", Param: []ast.Statement{float64(c.random(0, 1000))}},
		{Name: "Лев", Param: []ast.Statement{c.randomString(20), float64(c.random(1, 10))}},
		{Name: "Прав", Param: []ast.Statement{c.randomString(20), float64(c.random(1, 10))}},
		{Name: "Сред", Param: []ast.Statement{c.randomString(20), float64(c.random(1, 10)), float64(c.random(0, 10))}},
		{Name: "ПобитовыйСдвигВлево", Param: []ast.Statement{float64(c.random(0, 1000)), float64(c.random(1, 10))}},
		{Name: "ПобитовыйСдвигВправо", Param: []ast.Statement{float64(c.random(0, 1000)), float64(c.random(1, 10))}},
		{Name: "ПобитовоеИ", Param: []ast.Statement{float64(c.random(0, 1000)), float64(c.random(1, 10))}},
	}
	return pool[c.random(0, int64(len(pool)))]
}

func (c *Obfuscator) randomString(lenStr int) string {
	charset := []rune("абвгдежзийклмнопрстуфхцчшщъыьэюяАБВГДЕЖЗИЙКЛМНОПРСТУФХЦЧШЩЪЫЬЭЮЯ")
	builder := strings.Builder{}
	builder.Grow(lenStr)
	for i := 0; i < lenStr; i++ {
		builder.WriteRune(charset[c.r.Intn(len(charset))])
	}
	return builder.String()
}

func (c *Obfuscator) obfuscateString(str string, key int32) string {
	var decrypted []rune
	// ИЗМЕНЕНИЕ: Убрана опасная замена символа '|'
	for _, char := range str {
		decrypted = append(decrypted, char^key)
	}

	b := []byte(string(decrypted))
	return base64.StdEncoding.EncodeToString(b)
}

func (c *Obfuscator) newDecodeStringFunc(directive string) string {
	strParam := c.randomString(10)
	keyParam := c.randomString(10)
	returnName := c.randomString(10)
	funcName := c.randomString(30)
	iteratorVar := c.randomString(1)
	if iteratorVar == strParam || iteratorVar == keyParam || iteratorVar == returnName {
		iteratorVar = c.randomString(2) // Уменьшаем шанс коллизии
	}

	// Структура функции для расшифровки.
	// Использует побитовые операции для дополнительной маскировки.
	f := &ast.FunctionOrProcedure{
		Type: ast.PFTypeFunction,
		Name: funcName,
		Body: []ast.Statement{
			&ast.ExpStatement{
				Operation: ast.OpEq,
				Left:      ast.VarStatement{Name: "ДвоичныеДанные"},
				Right: c.hideValue(ast.MethodStatement{
					Name: "Base64Значение",
					Param: []ast.Statement{
						ast.VarStatement{Name: strParam},
					},
				}, 4),
			},
			&ast.ExpStatement{
				Operation: ast.OpEq,
				Left:      ast.VarStatement{Name: strParam},
				Right: c.hideValue(ast.MethodStatement{
					Name: "ПолучитьСтрокуИзДвоичныхДанных",
					Param: []ast.Statement{
						ast.VarStatement{Name: "ДвоичныеДанные"},
					},
				}, 4),
			},
			&ast.ExpStatement{
				Operation: ast.OpEq,
				Left:      ast.VarStatement{Name: returnName},
				Right:     c.hideValue("", 4),
			},
			&ast.LoopStatement{
				For: &ast.ExpStatement{
					Operation: ast.OpEq,
					Left:      ast.VarStatement{Name: iteratorVar},
					Right:     1.000000,
				},
				To: ast.MethodStatement{
					Name: "СтрДлина",
					Param: []ast.Statement{
						ast.VarStatement{Name: strParam},
					},
				},
				Body: []ast.Statement{
					&ast.ExpStatement{
						Operation: ast.OpEq,
						Left:      ast.VarStatement{Name: "КодСимвола"},
						Right: c.hideValue(ast.MethodStatement{
							Name: "КодСимвола",
							Param: []ast.Statement{
								ast.VarStatement{Name: strParam},
								ast.VarStatement{Name: iteratorVar},
							},
						}, 4),
					},
					&ast.ExpStatement{
						Operation: ast.OpEq,
						Left:      ast.VarStatement{Name: returnName},
						Right: &ast.ExpStatement{
							Operation: ast.OpPlus,
							Left:      ast.VarStatement{Name: returnName},
							Right: ast.MethodStatement{
								Name: "Символ",
								Param: []ast.Statement{
									// Побитовое исключающее ИЛИ (XOR) для расшифровки
									ast.MethodStatement{
										Name: "ПобитовоеИсключающееИЛИ",
										Param: []ast.Statement{
											ast.VarStatement{Name: "КодСимвола"},
											ast.VarStatement{Name: keyParam},
										},
									},
								},
							},
						},
					},
				},
			},
			&ast.ReturnStatement{
				Param: ast.VarStatement{
					Name: returnName,
				},
			},
		},
		Params: []ast.ParamStatement{
			{Name: strParam},
			{Name: keyParam},
		},
		Directive: directive,
	}

	c.appendGarbage(&f.Body)
	// Добавляем мусор в тело цикла
	if loop, ok := f.Body[3].(*ast.LoopStatement); ok {
		c.appendGarbage(&loop.Body)
	}

	// Заменяем цикл на GOTO, если включена опция
	if loop, ok := f.Body[3].(*ast.LoopStatement); ok {
		c.replaceLoopToGoto(&f.Body, loop, true)
	}

	// ИЗМЕНЕНИЕ: Не добавляем функцию сразу, а сохраняем для последующего добавления
	c.generatedFuncs = append(c.generatedFuncs, f)
	return funcName
}

func (c *Obfuscator) genCondition() {
	expression := func(op string) (string, bool, error) {
		left := c.randomMathExp(int(c.random(2, 5)))
		right := c.randomMathExp(int(c.random(2, 5)))
		fullExp := left + op + right

		evaluableExpression, err := govaluate.NewEvaluableExpression(fullExp)
		if err != nil {
			return "", false, err
		}

		result, err := evaluableExpression.Evaluate(nil)
		if err != nil {
			return "", false, err
		}

		if v, ok := result.(bool); ok {
			return fullExp, v, nil
		}

		return "", false, errors.New("expression did not evaluate to a boolean")
	}

	// Генератор "истинных" условий
	go func() {
		defer func() {
			// В случае паники (например, при закрытии канала) - выходим из горутины
			if r := recover(); r != nil {
				return
			}
		}()
		for {
			select {
			case <-c.ctx.Done():
				return
			default:
				if exp, ok, err := expression(">"); err == nil && ok {
					c.trueCondition <- exp
				}
				if exp, ok, err := expression("<"); err == nil && !ok { // !ok in this context means false, so we want the opposite
					c.trueCondition <- exp
				}
			}
		}
	}()

	// Генератор "ложных" условий
	go func() {
		defer func() {
			if r := recover(); r != nil {
				return
			}
		}()
		for {
			select {
			case <-c.ctx.Done():
				return
			default:
				if exp, ok, err := expression(">"); err == nil && !ok {
					c.falseCondition <- exp
				}
				if exp, ok, err := expression("<"); err == nil && ok {
					c.falseCondition <- exp
				}
			}
		}
	}()
}

func (c *Obfuscator) randomMathExp(lenExp int) string {
	if lenExp <= 0 {
		return strconv.Itoa(int(c.random(1, 1000)))
	}
	builder := strings.Builder{}
	operations := []string{"-", "+", "*"} // Убрал деление, чтобы избежать деления на ноль

	for i := 0; i < lenExp; i++ {
		builder.WriteString(strconv.Itoa(int(c.random(1, 1000))))
		if i < lenExp-1 {
			builder.WriteString(operations[c.random(0, int64(len(operations)))])
		}
	}
	return builder.String()
}

// convStrExpToExpStatement преобразует строку в узел AST.
// ВНИМАНИЕ: Эта функция очень неэффективна, так как каждый раз запускает полный парсинг.
// Для оптимизации стоит либо модифицировать библиотеку-парсер для разбора только выражений,
// либо кэшировать результаты.
func (c *Obfuscator) convStrExpToExpStatement(str string) (*ast.ExpStatement, error) {
	// Создаем временную процедуру, чтобы выражение было синтаксически корректным для парсера
	tempCode := fmt.Sprintf(`Процедура Временная() Если %s Тогда КонецЕсли; КонецПроцедуры`, str)
	astObj := ast.NewAST(tempCode)
	if err := astObj.Parse(); err != nil {
		return nil, errors.Wrap(err, "ast parse error in convStrExpToExpStatement")
	}

	// Извлекаем наше выражение из дерева
	if len(astObj.ModuleStatement.Body) > 0 {
		if proc, ok := astObj.ModuleStatement.Body[0].(*ast.FunctionOrProcedure); ok && len(proc.Body) > 0 {
			if ifStmt, ok := proc.Body[0].(*ast.IfStatement); ok {
				if exp, ok := ifStmt.Expression.(*ast.ExpStatement); ok {
					return exp, nil
				}
			}
		}
	}

	return nil, errors.New("could not extract expression from parsed temp code")
}

func (c *Obfuscator) loopToGoto(loop *ast.LoopStatement) []ast.Statement {
	startLabel := c.randomString(5)
	endLabel := c.randomString(5)
	start := &ast.GoToLabelStatement{Name: startLabel}
	end := &ast.GoToLabelStatement{Name: endLabel}

	// Цикл "Пока"
	if loop.WhileExpr != nil {
		invertedExp := c.invertExp(loop.WhileExpr)
		newBody := []ast.Statement{
			start,
			&ast.IfStatement{
				Expression: invertedExp,
				TrueBlock:  []ast.Statement{ast.GoToStatement{Label: end}},
			},
		}

		ast.StatementWalk(loop.Body, func(_ *ast.FunctionOrProcedure, statement *ast.Statement) {
			switch (*statement).(type) {
			case ast.ContinueStatement:
				*statement = ast.GoToStatement{Label: start}
			case ast.BreakStatement:
				*statement = ast.GoToStatement{Label: end}
			}
		})

		newBody = append(newBody, loop.Body...)
		newBody = append(newBody, ast.GoToStatement{Label: start}, end)
		return newBody
	}

	// Цикл "Для"
	if loop.To != nil {
		exp, ok := loop.For.(*ast.ExpStatement)
		if !ok {
			return []ast.Statement{loop}
		}

		newBody := []ast.Statement{
			exp,
			start,
			&ast.IfStatement{
				Expression: &ast.ExpStatement{
					Operation: ast.OpGt,
					Left:      exp.Left,
					Right:     loop.To,
				},
				TrueBlock: []ast.Statement{ast.GoToStatement{Label: end}},
			},
		}
		newBody = append(newBody, loop.Body...)
		newBody = append(newBody,
			&ast.ExpStatement{
				Operation: ast.OpEq,
				Left:      exp.Left,
				Right: &ast.ExpStatement{
					Operation: ast.OpPlus,
					Left:      exp.Left,
					Right:     float64(1),
				},
			},
			ast.GoToStatement{Label: start},
			end)
		return newBody
	}

	return []ast.Statement{loop}
}

func (c *Obfuscator) invertExp(exp ast.Statement) ast.Statement {
	if v, ok := exp.(ast.INot); ok {
		return v.Not()
	}
	// Оборачиваем любое другое выражение в "НЕ (...)"
	return ast.NewNot(exp)
}

func (c *Obfuscator) replaceLoopToGoto(body *[]ast.Statement, loop *ast.LoopStatement, force bool) {
	if c.conf.RepLoopByGoto || force {
		newStatements := c.loopToGoto(loop)
		for i := len(*body) - 1; i >= 0; i-- {
			if (*body)[i] == loop {
				// Заменяем старый узел цикла на новую последовательность с GOTO
				*body = append((*body)[:i], append(newStatements, (*body)[i+1:]...)...)
				break // Выходим, так как замена произведена
			}
		}
	}
}

// [min, max)
func (c *Obfuscator) random(min, max int64) int64 {
	if min >= max {
		return min
	}
	return min + c.r.Int63n(max-min)
}
