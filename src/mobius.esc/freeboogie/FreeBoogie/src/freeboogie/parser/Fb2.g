grammar Fb2;

@header {
  package freeboogie.parser; 
  import freeboogie.ast.*; 
  import freeboogie.tc.TypeUtils;
  import genericutils.Id;
  import java.math.BigInteger;

}
@lexer::header {
  package freeboogie.parser;
}

@parser::members {
  public String fileName = null; // the file being processed
  private FileLocation tokLoc(Token t) {
    return new FileLocation(fileName,t.getLine(),t.getCharPositionInLine()+1);
  }
  private FileLocation fileLoc(Ast a) {
    return a == null? FileLocation.unknown() : a.loc();
  }
  
  public boolean ok = true;
  
  @Override
  public void reportError(RecognitionException x) {
    ok = false;
    super.reportError(x);
  }

}

program returns [Declaration v]:
  declarations EOF { if(ok) $v=$declarations.v; }
;

declarations returns [Declaration v]:
                                                { $v=null; }
  | 'type' d=type_decl_tail                     { $v=$d.v; }
  | 'const' d=const_decl_tail                   { $v=$d.v; }
  | 'axiom' d=axiom_tail                        { $v=$d.v; }
  | 'function' d=function_decl_tail             { $v=$d.v; }
  | 'var' d=global_decl_tail                    { $v=$d.v; }
  | 'procedure' d=procedure_decl_tail           { $v=$d.v; }
  | 'implementation' d=implementation_decl_tail { $v=$d.v; }
;

type_decl_tail returns [Declaration v]:
    ID (
    (';' t1=declarations { if(ok) $v=TypeDecl.mk($ID.text,$t1.v,tokLoc($ID));})
  | (',' t2=type_decl_tail { if(ok) $v=TypeDecl.mk($ID.text,$t2.v,tokLoc($ID)); }))
;

const_decl_tail returns [Declaration v]:
    (u='unique')? ID ':' type (
    (';' t1=declarations    
      { if(ok) $v=ConstDecl.mk($ID.text,$type.v,$u!=null,$t1.v,tokLoc($ID)); })
  | (',' t2=const_decl_tail 
      { if(ok) $v=ConstDecl.mk($ID.text,$type.v,$u!=null,$t2.v,tokLoc($ID)); }))
;

function_decl_tail returns [Declaration v]:
  s=signature ';' declarations
    { if(ok) $v=Function.mk($s.v,$declarations.v,fileLoc($s.v)); }
;

axiom_tail returns [Declaration v]:
  ('<' tv=id_list '>')? e=expr ';' declarations 
    { if(ok) $v=Axiom.mk(Id.get("axiom"),$tv.v,$e.v,$declarations.v,fileLoc($e.v)); }
;

global_decl_tail returns [Declaration v]:
    ID ('<' tv=id_list '>')? ':' type (
    (';' t1=declarations     { if(ok) $v=VariableDecl.mk($ID.text,$type.v,$tv.v,$t1.v,tokLoc($ID)); })
  | (',' t2=global_decl_tail { if(ok) $v=VariableDecl.mk($ID.text,$type.v,$tv.v,$t2.v,tokLoc($ID)); }))
;

procedure_decl_tail returns [Declaration v]:
  s=signature ';'? spec_list body? t=declarations
    { if(ok) {
        Declaration proc_tail = $t.v;
        if ($body.v != null)
          proc_tail = Implementation.mk(TypeUtils.stripDep($s.v).clone(),$body.v,proc_tail,fileLoc($s.v));
        $v=Procedure.mk($s.v,$spec_list.v,proc_tail,fileLoc($s.v)); 
    }}
;
	
implementation_decl_tail returns [Declaration v]:
  s=signature body t=declarations
    { if(ok) $v = Implementation.mk($s.v,$body.v,$t.v,fileLoc($s.v)); }
;

signature returns [Signature v]:
  ID ('<' tv=id_list '>')? '(' (a=opt_id_type_list)? ')' 
  ('returns' '(' (b=opt_id_type_list)? ')')?
    { if(ok) $v = Signature.mk($ID.text,$a.v,$b.v,$tv.v,tokLoc($ID)); }
;

spec_list returns [Specification v]:
      { $v=null; }
  | (f='free')? 'requires' ('<' tv=id_list '>')? h=expr ';' t=spec_list
      { if(ok) $v=Specification.mk($tv.v,Specification.SpecType.REQUIRES,$h.v,$f!=null,$t.v,fileLoc($h.v)); }
  | 'modifies' t=modifies_tail
      { $v=$modifies_tail.v; }
  | (f='free')? 'ensures' ('<' tv=id_list '>')? h=expr ';' t=spec_list
      { if(ok) $v=Specification.mk($tv.v,Specification.SpecType.ENSURES,$h.v,$f!=null,$t.v,fileLoc($h.v)); }
;

modifies_tail returns [Specification v]:
    (f='free')? ids=id_list ';' t=spec_list { if (ok) {
      Identifiers x = $ids.v;
      Exprs e = null;
      while (x != null) {
        e = Exprs.mk(x.getId(), e);
        x = x.getTail();
      }
      $v=Specification.mk(null,Specification.SpecType.MODIFIES,e,$f!=null,$t.v,fileLoc($ids.v));
    }}
;
	
body returns [Body v]:
  '{' ('var' var_id_type_list)? b=block_list '}'
    { if(ok) $v = Body.mk($var_id_type_list.v,$b.v,fileLoc($b.v)); }
;

block_list returns [Block v]:
  ID ':' cl=command_list s=block_succ (t=block_list)?
    { if(ok) {
      String n_=$ID.text;
      Identifiers s_=$s.v;
      Block t_=$t.v;
      for (int i = $cl.v.size() - 1; i > 0; --i) {
        Command c_=$cl.v.get(i);
        String ss_=Id.get(n_);
        t_=Block.mk(ss_,c_,s_,t_,fileLoc(c_));
        s_=Identifiers.mk(AtomId.mk(ss_,null),null);
      }
      $v=Block.mk(n_,$cl.v.isEmpty()?null:$cl.v.get(0),s_,t_,tokLoc($ID));
    }}
;

block_succ returns [Identifiers v]:
    a='goto' id_list ';' 
      { if(ok) $v=$id_list.v; }
  |  a='return' ';'
      { if(ok) $v=null; }
;
	
command	returns [Command v]:
    a=atom_id i=index_list ':=' b=expr ';' 
      { if(ok) {
          Expr rhs = $b.v;
          ArrayList<Atom> lhs = new ArrayList<Atom>();
          lhs.add($a.v.clone());
          for (int k = 1; k < $i.v.size(); ++k)
            lhs.add(AtomMapSelect.mk(lhs.get(k-1).clone(), $i.v.get(k-1)));
          for (int k = $i.v.size()-1; k>=0; --k)
            rhs = AtomMapUpdate.mk(lhs.get(k).clone(), $i.v.get(k).clone(), rhs);
          $v=AssignmentCmd.mk($a.v,rhs,fileLoc($a.v));
      }}
  | t='assert' ('<' tv=id_list '>')? expr ';'
      { if(ok) $v=AssertAssumeCmd.mk(AssertAssumeCmd.CmdType.ASSERT,$tv.v,$expr.v,tokLoc($t)); }
  | t='assume' ('<' tv=id_list '>')? expr ';'
      { if(ok) $v=AssertAssumeCmd.mk(AssertAssumeCmd.CmdType.ASSUME,$tv.v,$expr.v,tokLoc($t)); }
  | t='havoc' id_list ';'
      { if(ok) $v=HavocCmd.mk($id_list.v,tokLoc($t));}
  | t='call' call_lhs
    n=ID ('<' st=quoted_simple_type_list '>')? '(' (r=expr_list)? ')' ';'
      { if(ok) $v=CallCmd.mk($n.text,$st.v,$call_lhs.v,$r.v,tokLoc($t)); }
;

call_lhs returns [Identifiers v]:
    (id_list ':=')=> il=id_list ':=' {$v=$il.v;}
  | {$v=null;}
;
	
index returns [Exprs v]:
  '[' expr_list ']' { $v = $expr_list.v; }
;

/* {{{ BEGIN expression grammar.

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
   ==> is right associative
   Others are left associative.
   The unary operators are ! and -.
   Typechecking takes care of booleans added to integers 
   and the like.
 */

expr returns [Expr v]:
  l=expr_a {$v=$l.v;} 
    (t='<==>' r=expr_a {if(ok) $v=BinaryOp.mk(BinaryOp.Op.EQUIV,$v,$r.v,tokLoc($t));})*
;

expr_a returns [Expr v]: 
  l=expr_b {$v=$l.v;} 
    (t='==>' r=expr_a {if(ok) $v=BinaryOp.mk(BinaryOp.Op.IMPLIES,$v,$r.v,tokLoc($t));})?
;

// TODO: these do not keep track of location quite correctly
expr_b returns [Expr v]:
  l=expr_c {$v=$l.v;} 
    (op=and_or_op r=expr_c {if(ok) $v=BinaryOp.mk($op.v,$v,$r.v,fileLoc($r.v));})*
;

expr_c returns [Expr v]:
  l=expr_d {$v=$l.v;}
    (op=comp_op r=expr_d {if(ok) $v=BinaryOp.mk($op.v,$v,$r.v,fileLoc($r.v));})*
;

expr_d returns [Expr v]:
  l=expr_e {$v=$l.v;}
    (op=add_op r=expr_e {if(ok) $v=BinaryOp.mk($op.v,$v,$r.v,fileLoc($r.v));})*
;

expr_e returns [Expr v]: 
  l=expr_f {$v=$l.v;}
    (op=mul_op r=expr_f {if(ok) $v=BinaryOp.mk($op.v,$v,$r.v,fileLoc($r.v));})*
;

expr_f returns [Expr v]:
    m=atom ('[' idx=expr_list (':=' val=expr)? ']')?
      { if (ok) {
        if ($idx.v == null) 
          $v=$m.v;
        else if ($val.v == null) 
          $v=AtomMapSelect.mk($m.v,$idx.v,fileLoc($m.v));
        else 
          $v=AtomMapUpdate.mk($m.v,$idx.v,$val.v,fileLoc($m.v));
      }}
  | '(' expr ')' {$v=$expr.v;}
  | t='-' a=expr_f   {if(ok) $v=UnaryOp.mk(UnaryOp.Op.MINUS,$a.v,tokLoc($t));}
  | t='!' a=expr_f   {if(ok) $v=UnaryOp.mk(UnaryOp.Op.NOT,$a.v,tokLoc($t));}
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
    t='false' { if(ok) $v = AtomLit.mk(AtomLit.AtomType.FALSE,tokLoc($t)); }
  | t='true'  { if(ok) $v = AtomLit.mk(AtomLit.AtomType.TRUE,tokLoc($t)); }
  | t='null'  { if(ok) $v = AtomLit.mk(AtomLit.AtomType.NULL,tokLoc($t)); }
  | t=INT     { if(ok) $v = AtomNum.mk(new BigInteger($INT.text),tokLoc($t)); }
  |	t=ID ('<' st=quoted_simple_type_list '>')? 
              { if(ok) $v = AtomId.mk($t.text,$st.v,tokLoc($t)); }
    ('(' (p=expr_list?) ')'
              { if(ok) $v = AtomFun.mk($t.text,$st.v,$p.v,tokLoc($t)); }
    )?
  | t='old' '(' expr ')'
              { if(ok) $v = AtomOld.mk($expr.v,tokLoc($t)); }
  | t='cast' '(' expr ',' type ')'
              { if(ok) $v = AtomCast.mk($expr.v, $type.v,tokLoc($t)); }
  | t='(' a=quant_op b=id_type_list '::' c=triggers d=expr ')'
              { if(ok) $v = AtomQuant.mk($a.v,$b.v,$c.v,$d.v,tokLoc($t)); }
;

atom_id returns [AtomId v]:
    ID ('<' st=quoted_simple_type_list '>')?
      { if(ok) $v = AtomId.mk($ID.text,$st.v,tokLoc($ID)); }
;

// END of the expression grammar }}}
	
quant_op returns [AtomQuant.QuantType v]:
    'forall' { $v = AtomQuant.QuantType.FORALL; }
  | 'exists' { $v = AtomQuant.QuantType.EXISTS; }
;

triggers returns [Trigger v]:
    { $v=null; }
  | a='{' (':' ID)? c=expr_list '}' d=triggers
      { if(ok) $v=Trigger.mk($ID==null?null:$ID.text,$c.v,$d.v,tokLoc($a)); }
;


// {{{ BEGIN list rules 
	
expr_list returns [Exprs v]:
  h=expr (',' t=expr_list)? { if(ok) $v = Exprs.mk($h.v, $t.v,fileLoc($h.v)); }
;

id_list	returns [Identifiers v]:	
    a=atom_id (',' r=id_list)? { if(ok) $v=Identifiers.mk($a.v,$r.v,fileLoc($a.v)); }
;

quoted_simple_type_list returns [TupleType v]:
    '`' h=simple_type (',' t=quoted_simple_type_list)?
  { if (ok) $v=TupleType.mk($h.v,$t.v,fileLoc($h.v)); }
;

simple_type_list returns [TupleType v]:
    h=simple_type (',' t=simple_type_list)?
  { if (ok) $v=TupleType.mk($h.v,$t.v,fileLoc($h.v)); }
;

opt_id_type_list returns [Declaration v]:
  (hi=ID ('<' tv=id_list '>')? ':')? ht=type (',' t=opt_id_type_list)? 
    { if(ok) $v = VariableDecl.mk($hi==null?Id.get("unnamed"):$hi.text, $ht.v, $tv.v,$t.v,fileLoc($ht.v)); }
;

id_type_list returns [Declaration v]:
  hi=ID ('<' tv=id_list '>')? ':' ht=type (',' t=id_type_list)? 
    { if(ok) $v = VariableDecl.mk($hi.text, $ht.v,$tv.v,$t.v,tokLoc($ID)); }
;

var_id_type_list returns [Declaration v]:
    ';' { $v = null; }
  | hi=ID ('<' tv=id_list '>')? ':' ht=type (','|';' 'var')? t=var_id_type_list
      { if(ok) $v = VariableDecl.mk($hi.text, $ht.v,$tv.v,$t.v,tokLoc($ID)); }
;

command_list returns [ArrayList<Command> v]:
  {if (ok) $v = new ArrayList<Command>();}
  (c=command {if (ok) $v.add($c.v);})*
;

index_list returns [ArrayList<Exprs> v]:
  {if (ok) $v = new ArrayList<Exprs>();}
  (i=index {if (ok) $v.add($i.v);})*
;
	
// END list rules }}}


simple_type returns [Type v]:
    t='bool' { if(ok) $v = PrimitiveType.mk(PrimitiveType.Ptype.BOOL,tokLoc($t)); }
  | t='int'  { if(ok) $v = PrimitiveType.mk(PrimitiveType.Ptype.INT,tokLoc($t)); }
  | t='ref'  { if(ok) $v = PrimitiveType.mk(PrimitiveType.Ptype.REF,tokLoc($t)); }
  | t='name' { if(ok) $v = PrimitiveType.mk(PrimitiveType.Ptype.NAME,tokLoc($t)); }
  | t='any'  { if(ok) $v = PrimitiveType.mk(PrimitiveType.Ptype.ANY,tokLoc($t)); }
  | t=ID     { if(ok) $v = UserType.mk($ID.text,tokLoc($t)); }
  | t='[' it=simple_type_list ']' et=simple_type
             { if(ok) $v = MapType.mk($it.v,$et.v,tokLoc($t)); }
  | t='<' p=simple_type '>' st=simple_type
             { if(ok) $v = IndexedType.mk($p.v,$st.v,tokLoc($t)); }
;

type returns [Type v]:
  t=simple_type ('where' p=expr)?
    {  if (ok) {
         if ($p.v==null) $v=$t.v;
         else $v=DepType.mk($t.v,$p.v,fileLoc($t.v));
    }}
;
	
ID:
  ('a'..'z'|'A'..'Z'|'\''|'~'|'#'|'$'|'.'|'?'|'_'|'^'|'\\')
  ('a'..'z'|'A'..'Z'|'\''|'~'|'#'|'$'|'.'|'?'|'_'|'^'|'`'|'0'..'9')*
;
	
INT     : 	'0'..'9'+ ;
WS      : 	(' '|'\t'|'\n'|'\r')+ {$channel=HIDDEN;};
COMMENT
    :   '/*' ( options {greedy=false;} : . )* '*/' {$channel=HIDDEN;}
    ;

LINE_COMMENT
    : '//' ~('\n'|'\r')* ('\r'|'\n') {$channel=HIDDEN;}
    ;

