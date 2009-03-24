" Vim syntax file
" Language:	BoogiePL
" Version: 0.1
" Last Change:	2008/12/19
" Maintainer:  Radu Grigore <radu.grigore@gmail.com>

if exists("b:current_syntax")
  finish
endif

syn case match
syn sync lines=250

syn keyword boogieplDeclaration type const unique function axiom var procedure implementation
syn keyword boogieplSpecification free requires ensures modifies
syn keyword boogieplCommand assert assume havoc call
syn keyword boogieplConstant false true null
syn keyword boogieplExpression old cast where
syn keyword boogieplLogic forall exists
syn keyword boogieplType bool int ref name any
syn keyword boogieplFlow return returns goto
syn keyword boogieplAttention contained	TODO BUG HACK NOTE

syn match boogieplComment /\/\/.*/ contains=boogieplAttention
syn match boogieplLabel /^\s*[a-zA-Z0-9_]\+\s*:\([^=]\|$\)/ 

syn region boogieplBlock start=/{/ end=/}/ contains=ALL
syn region boogieplBlockComment start=/\/\*/ end=/\*\// contains=boogieplAttention

hi def link boogieplDeclaration Type
hi def link boogieplSpecification Keyword
hi def link boogieplCommand Statement
hi def link boogieplConstant Constant
hi def link boogieplExpression Keyword
hi def link boogieplLogic Keyword
hi def link boogieplType Type
hi def link boogieplFlow Keyword
hi def link boogieplAttention Todo
hi def link boogieplComment Comment
hi def link boogieplBlockComment Comment
hi def link boogieplLabel Identifier

