module github.com/vasdmi666/Obfuscator-1C

go 1.22.4

toolchain go1.23.0

// replace github.com/LazarenkoA/1c-language-parser => C:\GoProject\1c-language-parser

require (
	github.com/LazarenkoA/1c-language-parser v0.0.0-20241111175329-8b0aa4e1f1f6
	github.com/google/uuid v1.6.0
	github.com/knetic/govaluate v3.0.0+incompatible
	github.com/pkg/errors v0.9.1
	github.com/stretchr/testify v1.8.4
)

require (
	github.com/davecgh/go-spew v1.1.1 // indirect
	github.com/pmezard/go-difflib v1.0.0 // indirect
	gopkg.in/yaml.v3 v3.0.1 // indirect
)
