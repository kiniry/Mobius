grammar Fb;

@header {package freeboogie.parser; import freeboogie.ast.*;}
@lexer::header {package freeboogie.parser;}

@parser::members {
  public String fileName = null; // the file being processed
  private AstLocation tokLoc(Token t) {
    return new AstLocation(fileName,t.getLine(),t.getCharPositionInLine());
  }
}

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
    (';' t1=declarations {$v=new TypeDecl($ID.text,$t1.v,tokLoc($ID));})
  | (',' t2=type_decl_tail { $v=new TypeDecl($ID.text,$t2.v,tokLoc($ID)); }))
;

const_decl_tail returns [Declaration v]:
    ID ':' type (
    (';' t1=declarations    { $v=new ConstDecl($ID.text,$type.v,$t1.v,tokLoc($ID)); })
  | (',' t2=const_decl_tail { $v=new ConstDecl($ID.text,$type.v,$t2.v,tokLoc($ID)); }))
;

function_decl_tail returns [Declaration v]:
  s=signature ';' declarations
    { $v=new Function($s.v,$declarations.v,$s.v.loc()); }
;

axiom_tail returns [Declaration v]:
  e=expr ';' declarations { $v=new Axiom($e.v,$declarations.v,$e.v.loc()); }
;

global_decl_tail returns [Declaration v]:
    ID ':' type (
    (';' t1=declarations     { $v=new VariableDecl($ID.text,$type.v,$t1.v,tokLoc($ID)); })
  | (',' t2=global_decl_tail { $v=new VariableDecl($ID.text,$type.v,$t2.v,tokLoc($ID)); }))
;

procedure_decl_tail returns [Declaration v]:
  s=signature ';'? spec_list body? t=declarations
    { $v=new Procedure($s.v,$spec_list.v,$body.v,$t.v,$s.v.loc()); }
;
	
// TODO: check that the signature has names?
implementation_decl_tail returns [Declaration v]:
  s=signature body t=declarations
    { $v = new Implementation($s.v,$body.v,$t.v,$s.v.loc()); }
;

signature returns [Signature v]:
  ID '(' (a=opt_id_type_list)? ')' ('returns' '(' (b=opt_id_type_list)? ')')?
    { $v = new Signature($ID.text,$a.v,$b.v,tokLoc($ID)); }
;

spec_list returns [Specification v]:
      { $v=null; }
  | (f='free')? 'requires' h=expr ';' t=spec_list
      { $v=new Specification(Specification.SpecType.REQUIRES,$h.v,$f!=null,$t.v,$h.v.loc()); }
  | 'modifies' t=modifies_tail
      { $v=$modifies_tail.v; }
  | (f='free')? 'ensures' h=expr ';' t=spec_list
      { $v=new Specification(Specification.SpecType.ENSURES,$h.v,$f!=null,$t.v,$h.v.loc()); }
;

modifies_tail returns [Specification v]:
    ';' spec_list { $v = $spec_list.v; }
  | h=atom_id ','? t=modifies_tail
      { $v=new Specification(Specification.SpecType.MODIFIES,$h.v,false,$t.v,$h.v.loc()); }
;
	
body returns [Body v]:
  '{' ('var' var_id_type_list)? b=block_list '}'
    { $v = new Body($var_id_type_list.v,$b.v,$b.v.loc()); }
;

block_list returns [Block v]:
  ID ':' (command_list)? block_end (block_list)?
    { $v=new Block($ID.text,$command_list.v,$block_end.v,$block_list.v,tokLoc($ID));}
;

block_end returns [BlockEnd v]:
    a='goto' id_list ';' 
      { $v=new BlockEnd(BlockEnd.BlockType.GOTO, $id_list.v,tokLoc($a)); }
  |  a='return' ';'
      { $v=new BlockEnd(BlockEnd.BlockType.RETURN, null,tokLoc($a)); }
;
	
command	returns [Command v]:
    a=atom_id (i=index)? ':=' b=expr ';' 
      { Atom lhs = $a.v;
        if ($i.v!=null) lhs=new AtomIdx(lhs,$i.v,$a.v.loc());
        $v=new AssignmentCmd(lhs,$b.v,$a.v.loc());
      }
  | t='assert' expr ';'
      { $v=new AssertAssumeCmd(AssertAssumeCmd.CmdType.ASSERT,$expr.v,tokLoc($t)); }
  | t='assume' expr ';'
      { $v=new AssertAssumeCmd(AssertAssumeCmd.CmdType.ASSUME,$expr.v,tokLoc($t)); }
  | t='havoc' ID ';'
      {$v=new HavocCmd($ID.text,tokLoc($t));}
  | t='call' (l=id_list ':=')? ID '(' (r=expr_list)? ')' ';'
      {$v=new CallCmd($ID.text,$l.v,$r.v,tokLoc($t));}
;
	
index returns [Index v]:
  '[' a=expr (',' b=expr)? ']' { $v = new Index($a.v, $b.v,$a.v.loc()); }
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
    (t='<==>' r=expr_a {$v=new BinaryOp(BinaryOp.Op.EQUIV,$v,$r.v,tokLoc($t));})*
;

expr_a returns [Expr v]: 
  l=expr_b {$v=$l.v;} 
    (t='==>' r=expr_b {$v=new BinaryOp(BinaryOp.Op.IMPLIES,$v,$r.v,tokLoc($t));})*
;

// TODO: these does not keep track of location quite correctly
expr_b returns [Expr v]:
  l=expr_c {$v=$l.v;} 
    (op=and_or_op r=expr_c {$v=new BinaryOp($op.v,$v,$r.v,$r.v.loc());})*
;

expr_c returns [Expr v]:
  l=expr_d {$v=$l.v;}
    (op=comp_op r=expr_d {$v=new BinaryOp($op.v,$v,$r.v,$r.v.loc());})*
;

expr_d returns [Expr v]:
  l=expr_e {$v=$l.v;}
    (op=add_op r=expr_e {$v=new BinaryOp($op.v,$v,$r.v,$r.v.loc());})*
;

expr_e returns [Expr v]: 
  l=expr_f {$v=$l.v;}
    (op=mul_op r=expr_f {$v=new BinaryOp($op.v,$v,$r.v,$r.v.loc());})*
;

expr_f returns [Expr v]:
    atom index? 
      { if ($index.v==null) $v=$atom.v;
        else $v=new AtomIdx($atom.v,$index.v,$atom.v.loc());
      }
  | '(' expr ')' {$v=$expr.v;}
  | t='-' expr_f   {$v=new UnaryOp(UnaryOp.Op.MINUS,$expr_f.v,tokLoc($t));}
  | t='!' expr_f   {$v=new UnaryOp(UnaryOp.Op.NOT,$expr_f.v,tokLoc($t));}
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
    t='false' { $v = new AtomLit(AtomLit.AtomType.FALSE,tokLoc($t)); }
  | t='true'  { $v = new AtomLit(AtomLit.AtomType.TRUE,tokLoc($t)); }
  | t='null'  { $v = new AtomLit(AtomLit.AtomType.NULL,tokLoc($t)); }

  // TODO: What type of integers do I need for boogie? Maybe BigInteger?
  | t=INT     { $v = new AtomNum(Integer.parseInt($INT.text),tokLoc($t)); }
  | atom_id   { $v = $atom_id.v; }
  |	t=ID '(' (expr_list?) ')'
              { $v = new AtomFun($ID.text, $expr_list.v,tokLoc($t)); }
  | t='old' '(' expr ')'
              { $v = new AtomOld($expr.v,tokLoc($t)); }
  | t='cast' '(' expr ',' type ')'
              { $v = new AtomCast($expr.v, $type.v,tokLoc($t)); }

  // TODO: the triggers are ignored now
  | t='(' quant_op id_type_list '::' triggers expr ')'
              { $v = new AtomQuant($quant_op.v, $id_type_list.v, $expr.v,tokLoc($t)); }
;

atom_id returns [AtomId v]:
    ID      { $v = new AtomId($ID.text,tokLoc($ID)); }
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
  h=expr (',' t=expr_list)? { $v = new Exprs($h.v, $t.v,$h.v.loc()); }
;

id_list	returns [Identifiers v]:	
    ID (',' r=id_list)? { $v=new Identifiers($ID.text,$r.v,tokLoc($ID)); }
;

opt_id_type_list returns [Declaration v]:
  (hi=ID ':')? ht=type (',' t=opt_id_type_list)? 
    { $v = new VariableDecl(($hi==null)?null:$hi.text, $ht.v, $t.v,$ht.v.loc()); }
;

id_type_list returns [Declaration v]:
  hi=ID ':' ht=type (',' t=id_type_list)? 
    { $v = new VariableDecl($hi.text, $ht.v, $t.v,tokLoc($ID)); }
;

var_id_type_list returns [Declaration v]:
    ';' { $v = null; }
  | hi=ID ':' ht=type (','|';' 'var')? t=var_id_type_list
      { $v = new VariableDecl($hi.text, $ht.v, $t.v,tokLoc($ID)); }
;

command_list returns [Commands v]:
  h=command (t=command_list)? { $v=new Commands($h.v,$t.v,$h.v.loc()); }
;
	
// END list rules 


simple_type returns [Type v]:
    t='bool' { $v = new PrimitiveType(PrimitiveType.Ptype.BOOL,tokLoc($t)); }
  | t='int'  { $v = new PrimitiveType(PrimitiveType.Ptype.INT,tokLoc($t)); }
  | t='ref'  { $v = new PrimitiveType(PrimitiveType.Ptype.REF,tokLoc($t)); }
  | t='name' { $v = new PrimitiveType(PrimitiveType.Ptype.NAME,tokLoc($t)); }
  | t='any'  { $v = new PrimitiveType(PrimitiveType.Ptype.ANY,tokLoc($t)); }
  | t=ID     { $v = new UserType($ID.text,tokLoc($t)); }
  | t='[' r=simple_type (',' c=simple_type)? ']' e=simple_type
             { $v = new ArrayType($r.v,$c.v,$e.v,tokLoc($t)); }
  | t='<' p=simple_type '>' st=simple_type
             { $v = new GenericType($p.v,$st.v,tokLoc($t)); }
;

type returns [Type v]:
  t=simple_type ('where' p=expr)?
    {  if ($p.v==null) $v=$t.v;
       else $v=new DepType($t.v,$p.v,$t.v.loc());
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
