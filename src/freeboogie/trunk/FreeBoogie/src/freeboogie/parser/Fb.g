grammar Fb;

@header {package freeboogie.parser; import freeboogie.ast.*;}
@lexer::header {package freeboogie.parser;}

program returns [Declaration v]:
  declarations EOF { $v=$declarations.v; }
;

declarations returns [Declaration v]:
                                                { $v=null; }
  | 'type' d=type_decl_tail                     { $v=$d.v; }
  | 'const' d=const_decl_tail                   { $v=$d.v; }
  | 'function' d=function_decl_tail             { $v=$d.v; }
  | 'axiom' d=axiom_tail                        { $v=$d.v; }
  | 'var' d=global_decl_tail                    { $v=$d.v; }
  | 'procedure' d=procedure_decl_tail           { $v=$d.v; }
  | 'implementation' d=implementation_decl_tail { $v=$d.v; }
;

type_decl_tail returns [Declaration v]:
    ID (
    (';' t1=declarations {$v=new TypeDecl($ID.text,$t1.v);})
  | (',' t2=type_decl_tail { $v=new TypeDecl($ID.text,$t2.v); }))
;

const_decl_tail returns [Declaration v]:
    ID ':' type (
    (';' t1=declarations    { $v=new ConstDecl($ID.text,$type.v,$t1.v); })
  | (',' t2=const_decl_tail { $v=new ConstDecl($ID.text,$type.v,$t2.v); }))
;

function_decl_tail returns [Declaration v]:
  signature ';' declarations
    { $v=new Function($signature.v,$declarations.v); }
;

axiom_tail returns [Declaration v]:
  expr ';' declarations { $v=new Axiom($expr.v,$declarations.v); }
;

global_decl_tail returns [Declaration v]:
    ID ':' type (
    (';' t1=declarations     { $v=new VariableDecl($ID.text,$type.v,$t1.v); })
  | (',' t2=global_decl_tail { $v=new VariableDecl($ID.text,$type.v,$t2.v); }))
;

procedure_decl_tail returns [Declaration v]:
  signature ';'? spec_list body? t=declarations
    { $v=new Procedure($signature.v,$spec_list.v,$body.v,$t.v); }
;
	
// TODO: check that the signature has names?
implementation_decl_tail returns [Declaration v]:
  signature body t=declarations
    { $v = new Implementation($signature.v,$body.v,$t.v); }
;

signature returns [Signature v]:
  ID '(' (a=opt_id_type_list)? ')' ('returns' '(' (b=opt_id_type_list)? ')')?
    { $v = new Signature($ID.text,$a.v,$b.v); }
;

// TODO: Add 'free' in the abstract grammar, perhaps as a boolean.
spec_list returns [Specification v]:
      { $v=null; }
  | 'free'? 'requires' h=expr ';' t=spec_list
      { $v=new Specification(Specification.SpecType.REQUIRES,$h.v,$t.v); }
  | 'modifies' t=modifies_tail
      { $v=$modifies_tail.v; }
  | 'free'? 'ensures' h=expr ';' t=spec_list
      { $v=new Specification(Specification.SpecType.ENSURES,$h.v,$t.v); }
;

modifies_tail returns [Specification v]:
    ';' spec_list { $v = $spec_list.v; }
  | h=atom_id ','? t=modifies_tail
      { $v=new Specification(Specification.SpecType.MODIFIES,$h.v,$t.v); }
;
	
body returns [Body v]:
  '{' ('var' var_id_type_list)? block_list '}'
    { $v = new Body($var_id_type_list.v, $block_list.v); }
;

block_list returns [Blocks v]:
  ID ':' (command_list)? block_end (block_list)?
    { $v=new Blocks($ID.text,$command_list.v,$block_end.v,$block_list.v);}
;

block_end returns [BlockEnd v]:
    'goto' id_list ';' 
      { $v=new BlockEnd(BlockEnd.BlockType.GOTO, $id_list.v); }
  |  'return' ';'
      { $v=new BlockEnd(BlockEnd.BlockType.RETURN, null); }
;
	
command	returns [Command v]:
    a=atom_id (i=index)? ':=' b=expr ';' 
      { Atom lhs = $a.v;
        if ($i.v!=null) lhs=new AtomIdx(lhs,$i.v);
        $v=new AssignmentCmd(lhs,$b.v);
      }
  | 'assert' expr ';'
      { $v=new AssertAssumeCmd(AssertAssumeCmd.CmdType.ASSERT,$expr.v); }
  | 'assume' expr ';'
      { $v=new AssertAssumeCmd(AssertAssumeCmd.CmdType.ASSUME,$expr.v); }
  | 'havoc' ID ';'
      {$v=new HavocCmd($ID.text);}
  | 'call' (l=id_list ':=')? ID '(' (r=expr_list)? ')' ';'
      {$v=new CallCmd($ID.text,$l.v,$r.v);}
;
	
index returns [Index v]:
  '[' a=expr (',' b=expr)? ']' { $v = new Index($a.v, $b.v); }
;

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

   <==> is associative
   Others are left associative.
   (TODO: shouldn't ==> be right associative?)
   The unary operators are ! and -.
   Typechecking takes care of booleans added to integers 
   and the like.
 */

// TODO: Check what kind of associativity these rules give.
// (I believe it is left)
expr returns [Expr v]:
  l=expr_a {$v=$l.v;} 
    ('<==>' r=expr_a {$v=new BinaryOp(BinaryOp.Op.EQUIV,$v,$r.v);})*
;

expr_a returns [Expr v]: 
  l=expr_b {$v=$l.v;} 
    ('==>' r=expr_b {$v=new BinaryOp(BinaryOp.Op.IMPLIES,$v,$r.v);})*
;

expr_b returns [Expr v]:
  l=expr_c {$v=$l.v;} 
    (op=and_or_op r=expr_c {$v=new BinaryOp($op.v,$v,$r.v);})*
;

expr_c returns [Expr v]:
  l=expr_d {$v=$l.v;}
    (op=comp_op r=expr_d {$v=new BinaryOp($op.v,$v,$r.v);})*
;

expr_d returns [Expr v]:
  l=expr_e {$v=$l.v;}
    (op=add_op r=expr_e {$v=new BinaryOp($op.v,$v,$r.v);})*
;

expr_e returns [Expr v]: 
  l=expr_f {$v=$l.v;}
    (op=mul_op r=expr_f {$v=new BinaryOp($op.v,$v,$r.v);})*
;

expr_f returns [Expr v]:
    atom index? 
      { if ($index.v==null) $v=$atom.v;
        else $v=new AtomIdx($atom.v,$index.v);
      }
  | '(' expr ')' {$v=$expr.v;}
  | '-' expr_f   {$v=new UnaryOp(UnaryOp.Op.MINUS,$expr_f.v);}
  | '!' expr_f   {$v=new UnaryOp(UnaryOp.Op.NOT,$expr_f.v);}
;

and_or_op returns [BinaryOp.Op v]:
    '&&' { $v = BinaryOp.Op.AND; }
  | '||' { $v = BinaryOp.Op.OR; }
;

comp_op returns [BinaryOp.Op v]:
    '==' { $v = BinaryOp.Op.EQ; }
  | '!=' { $v = BinaryOp.Op.NEQ; }
  | '<'  { $v = BinaryOp.Op.LT; }
  | '<=' { $v = BinaryOp.Op.LE; }
  | '>=' { $v = BinaryOp.Op.GE; }
  | '>'  { $v = BinaryOp.Op.GT; }
  | '<:' { $v = BinaryOp.Op.SUBTYPE; }
;

add_op returns [BinaryOp.Op v]:
    '+' { $v = BinaryOp.Op.PLUS; }
  | '-' { $v = BinaryOp.Op.MINUS; }
;

mul_op returns [BinaryOp.Op v]:
    '*' { $v = BinaryOp.Op.MUL; }
  | '/' { $v = BinaryOp.Op.DIV; }
  | '%' { $v = BinaryOp.Op.MOD; }
;

atom returns [Atom v]:
    'false' { $v = new AtomLit(AtomLit.AtomType.FALSE); }
  | 'true'  { $v = new AtomLit(AtomLit.AtomType.TRUE); }
  | 'null'  { $v = new AtomLit(AtomLit.AtomType.NULL); }
  | INT     { $v = new AtomNum(Integer.parseInt($INT.text)); }
  | atom_id { $v = $atom_id.v; }
  |	ID '(' (expr_list?) ')'
            { $v = new AtomFun($ID.text, $expr_list.v); }
  | 'old' '(' expr ')'
            { $v = new AtomOld($expr.v); }
  | 'cast' '(' expr ',' type ')'
            { $v = new AtomCast($expr.v, $type.v); }

  // TODO: the triggers are ignored now
  | '(' quant_op id_type_list '::' triggers expr ')'
            { $v = new AtomQuant($quant_op.v, $id_type_list.v, $expr.v); }
;

atom_id returns [AtomId v]:
    ID      { $v = new AtomId($ID.text); }
;

// END of the expression grammar 
	
quant_op returns [AtomQuant.QuantType v]:
    'forall' { $v = AtomQuant.QuantType.FORALL; }
  | 'exists' { $v = AtomQuant.QuantType.EXISTS; }
;

triggers:
  ('{' ':nopats'? expr_list '}')*
;


// BEGIN list rules 
	
expr_list returns [Exprs v]:
  h=expr (',' t=expr_list)? { $v = new Exprs($h.v, $t.v); }
;

id_list	returns [Identifiers v]:	
    ID (',' r=id_list)? { $v=new Identifiers($ID.text,$r.v); }
;

opt_id_type_list returns [Declaration v]:
  (hi=ID ':')? ht=type (',' t=opt_id_type_list)? 
    { $v = new VariableDecl(($hi==null)?null:$hi.text, $ht.v, $t.v); }
;

id_type_list returns [Declaration v]:
  hi=ID ':' ht=type (',' t=id_type_list)? 
    { $v = new VariableDecl($hi.text, $ht.v, $t.v); }
;

var_id_type_list returns [Declaration v]:
    ';' { $v = null; }
  | hi=ID ':' ht=type (','|';' 'var')? t=var_id_type_list
      { $v = new VariableDecl($hi.text, $ht.v, $t.v); }
;

command_list returns [Commands v]:
  h=command (t=command_list)? { $v=new Commands($h.v,$t.v); }
;
	
// END list rules 


simple_type returns [Type v]:
    'bool' { $v = new PrimitiveType(PrimitiveType.Ptype.BOOL); }
  | 'int'  { $v = new PrimitiveType(PrimitiveType.Ptype.INT); }
  | 'ref'  { $v = new PrimitiveType(PrimitiveType.Ptype.REF); }
  | 'name' { $v = new PrimitiveType(PrimitiveType.Ptype.NAME); }
  | 'any'  { $v = new PrimitiveType(PrimitiveType.Ptype.ANY); }
  | ID     { $v = new UserType($ID.text); }
  | '[' r=simple_type (',' c=simple_type)? ']' e=simple_type
           { $v = new ArrayType($r.v,$c.v,$e.v); }
  | '<' p=simple_type '>' t=simple_type
           { $v = new GenericType($p.v,$t.v); }
;

type returns [Type v]:
  t=simple_type ('where' p=expr)?
    {  if ($p.v==null) $v=$t.v;
       else $v=new DepType($t.v,$p.v);
    }
;
	
ID:
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
