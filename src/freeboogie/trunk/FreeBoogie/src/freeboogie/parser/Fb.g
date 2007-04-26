grammar Fb;

@header {package freeboogie.parser;}
@lexer::header {package freeboogie.parser;}

program	:	 decl* EOF;

decl	:	type_decl|constant|function|axiom|variable|procedure|implementation;

type_decl   
    :   'type' id_list ';';

constant:	'const' id_type_list ';';

function
    :   'function' id_list '(' (opt_id_type_list)? ')' 
        'returns' '(' (opt_id_type)? ')' ';';

axiom	:	'axiom' expr ';';

variable:	'var' id_type_list ';';

/* NOTE that this is a bit more permissive than what appears in the
   deline2005btp technical report. */
procedure
    :   'procedure' ID signature ';'? spec* body?
	;
	
signature
	:	'(' (id_type_list)? ')' ('returns' '(' (id_type_list)? ')')?;

spec
    :	'free'? 'requires' expr ';'
    |	'modifies' (id_list)?';'
    |	'free'? 'ensures' expr ';';
	
implementation
    :   'implementation' ID signature body;
	
body	:	'{' local_var_decl* block+ '}';

local_var_decl
	:	'var' id_type_list ';';
	
block	:	ID ':' command* block_end;

block_end
	:	'goto' id_list ';'
	|	'return' ';';
	
command	
    :	ID ':=' expr ';'
    |	ID index ':=' expr ';'
    |	'assert' expr ';'
    |	'assume' expr ';'
    |	'havoc' id_list ';'
    | 	'call' (id_list ':=')? ID '(' (expr_list)? ')' ';'
    ;
	
index 	
    :   '[' expr (',' expr)? ']';


/* BEGIN expression grammar.

   See http://www.engr.mun.ca/~theo/Misc/exp_parsing.htm
   for a succint presentation of how to implement precedence
   and associativity in a LL-grammar, the classical way.

   The precedence increases
     <==>
     ==>
     &&, ||
     =, !=, <, <=, >=, >, <:
     +, -
     *, /, %

   All are left associative
   The unary operators are ! and -.
   Typechecking takes care of booleans added to integers 
   and the like.
 */

expr:   expr_a ('<==>' expr_a)*;
expr_a: expr_b ('==>' expr_b)*;
expr_b: expr_c (('&&'|'||') expr_c)*;
expr_c: expr_d (('=='|'!='|'<'|'<='|'>='|'>'|'<:') expr_d)*;
expr_d: expr_e (('+'|'-') expr_e)*;
expr_e: expr_f (('*'|'/'|'%') expr_f)*;
expr_f: atom index? | '(' expr ')' | '-' expr_f | '!' expr_f;

atom
	:	'false'
	|	'true'
	|	'null'
	|	INT
	|	ID 
	|	ID '(' (expr_list?) ')'
	|	'old' '(' expr ')'
	|	'cast' '(' expr ',' type ')'
	|	quantification
	;

/* END of the expression grammar */

	
quantification
	:	'(' quant_op id_type_list '::' triggers expr ')';
	
quant_op:	'forall' | 'exists';

triggers
    :   ('{' ':nopats'? expr_list '}')*;


/* BEGIN list rules */
	
expr_list
	:	expr (',' expr_list)?;

id_list	:	ID (',' id_list)?;

opt_id_type_list
	:	opt_id_type (',' opt_id_type_list)?;

id_type_list
	:	id_type (',' id_type_list)?;
	
/* END list rules */


id_type	:	ID ':' type;

opt_id_type
	:	(ID ':')? type;


simple_type
    :	'bool'
    |	'int'
    |	'ref'
    |	'name'
    |	ID
    |	'any'
    |	'[' simple_type (',' simple_type)? ']' simple_type
    |   '<' simple_type '>' simple_type
    ;

type
    : simple_type ('where' expr)?;
	

ID      : 	
		('a'..'z'|'A'..'Z'|'\''|'~'|'#'|'$'|'.'|'?'|'_'|'^') 
		('a'..'z'|'A'..'Z'|'\''|'~'|'#'|'$'|'.'|'?'|'_'|'^'|'`'|'0'..'9')*
	;
	
INT     : 	'0'..'9'+ ;
WS      : 	(' '|'\t'|'\n'|'\r')+ {$channel=HIDDEN;};
COMMENT
    :   '/*' ( options {greedy=false;} : . )* '*/' {$channel=HIDDEN;}
    ;

LINE_COMMENT
    : '//' ~('\n'|'\r')* '\r'? '\n' {$channel=HIDDEN;}
    ;
