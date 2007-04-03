grammar Fb;

@header { package freeboogie.parser; }
@lexer::header {package freeboogie.parser;}

program	:	 decl*;

decl	:	type_decl|constant|function|axiom|variable|procedure|implementation;

type_decl   
    :   'type' id_list ';';

constant:	'const' id_type_list ';';

function:	'function' id_list '(' (opt_id_type_list)? ')' 'returns' '(' opt_id_type ')' ';';

axiom	:	'axiom' expr;

variable:	'var' id_type_list ';';

procedure
	:	'procedure' ID signature ';' spec*
//	|	'procedure' ID signature spec* body
	;
	
signature
	:	'(' id_type_list ')' ('returns' '('id_type_list ')')?;

spec	:	'requires' expr ';'
	|	'modifies' (id_list)?';'
	|	'ensures' expr ';';
	
implementation
	:	'implementation' ID signature body;
	
body	:	'{' local_var_decl* block+ '}';

local_var_decl
	:	'var' id_type_list ';';
	
block	:	ID ':' command* block_end;

block_end
	:	'goto' id_list ';'
	|	'return' ';';
	
command	:	ID ':=' expr ';'
	|	ID index ':=' expr ';'
	|	'assert' expr ';'
	|	'assume' expr ';'
	|	'havoc' id_list ';'
	| 	'call' (id_list ':=')? ID '(' (expr_list)? ')' ';'
	;
	
index 	:	'[' expr ']'
/*	|	'[' expr ',' expr ']'*/
	;

expr	:	equivalence;

equivalence
	:	implication ('<==>' equivalence)?;
	
implication
	:	logical_expr ('==>' implication)?;
	
logical_expr
	:	relation
/*	|	relation '&&' and_expr*/
/*	|	relation '||' or_expr*/
	;
	
//and_expr:	relation ('&&' and_expr)?;

//or_expr	:	relation ('||' or_expr)?;

relation:	term (rel_op term)?;

term	:	factor (add_op term)?;

factor	:	unary_expr (mul_op factor)?;

unary_expr
	:	atom index+
	|	'!' unary_expr
	| 	'-' unary_expr
	;
	
atom	:	'false'
	|	'true'
	|	'null'
	|	INT
	|	ID
	|	ID '(' (expr_list?) ')'
	|	'old' '(' expr ')'
	|	'cast' '(' expr ',' type ')'
	|	quantification
	|	'(' expr ')'
	;
	
quantification
	:	'(' quant_op id_type_list '::' expr ')';
	
rel_op	:	'='|'!='|'<'|'<='|'>='|'>'|'<:';

add_op	:	'+' | '-';

mul_op	:	'*' | '/' | '%';

quant_op:	'forall' | 'exists';
	
expr_list
	:	expr (',' expr_list)?;

id_list	:	ID (',' id_list)?;

opt_id_type_list
	:	opt_id_type (',' opt_id_type_list)?;

id_type_list
	:	id_type (',' id_type_list)?;
	
id_type	:	ID ':' type;

opt_id_type
	:	(ID ':')? type;


type	:	'bool'
	|	'int'
	|	'ref'
	|	'name'
	|	ID
	|	'any'
	|	'[' type (',' type)? ']' type
	;
	

ID      : 	
		('a'..'z'|'A'..'Z'|'\''|'~'|'#'|'$'|'.'|'?'|'_'|'^') 
		('a'..'z'|'A'..'Z'|'\''|'~'|'#'|'$'|'.'|'?'|'_'|'^'| '0'..'9')*
	;
	
ALPHA	:	;
INT     : 	'0'..'9'+ ;
WS      : 	(' '|'\t'|'\n')+ {$channel=HIDDEN;};
