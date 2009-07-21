" Vim syntax file
" Language:    ANTLR 3
" Maintainer:  Radu Grigore <radugrigore@gmail.com>
" Version:     0.0
" Last Change: 18 Mar 2008

" TODO: How to detect that the file is ANTLR? (pccts has the same extension)
" TODO: Is it possible to figure out the language in semantic actions?

" Magic incantation from the VIM7 user manual
if exists("b:current_syntax")
   finish
endif

" Assume that the code inside semantic actions is Java
syn include @javaCode <sfile>:p:h/java.vim
syn region antlrAction start=/{/ end=/}/ contains=@javaCode,antlrAction,antlrId

" Some keywords
syn keyword antlrKeywords options tokens parser lexer tree grammar header
syn keyword antlrKeywords protected public private returns throws exception

" Operators
syn match antlrOp /|\|\*\|?\|:\|\~/
syn match antlrId /\$\w\+/

" Inlined tokens
syn region antlrToken1 start=/'/ end=/'/ skip=/\\'/
syn region antlrToken2 start=/"/ end=/"/ skip=/\\"/

" Comments
syn match antlrComment /\/\/.*/
syn region antlrBlockComment start='/\*' end='\*/'

" The colors
hi def link antlrToken1       String
hi def link antlrToken2       String
hi def link antlrKeywords     Keyword
hi def link antlrComment      Comment
hi def link antlrBlockComment Comment
hi def link antlrOp           Operator
hi def link antlrId           Identifier

" Magic incantation from section 44.12 in the VIM7 user manual
let b:current_syntax = "antlr"

" vim:spell:et:sw=3:ts=3:
