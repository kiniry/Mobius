grammar Generic;


@header {
package mobius.logic.lang.generic.parser; 

import mobius.logic.lang.generic.ast.*;
import mobius.logic.lang.generic.*;
import java.util.LinkedList;
}

@lexer::header {
package mobius.logic.lang.generic.parser; 
}

@members {
 // No members
}

prog returns [ClauseList l]: 
         clause_list EOF {$l = $clause_list.list;};

clause_list returns [ClauseList list]: 
            clause l=clause_list {$list = $l.list;
                                  $list.getList().addFirst($clause.c);}
           |{$list = ClauseList.mk(new LinkedList<GenericAst>());};

clause returns [GenericAst c]: 
        DOC
        {$c = Doc.mk($DOC.text);} 
      | ATOM COLON expr // formula
        {$c = Clause.mk($ATOM.text, $expr.t);}
      | ATOM // symbol def
        {$c = Clause.mk($ATOM.text, Atom.mk(null, GType.TopType));}
      ;
      
expr returns [Term t]: 
      ATOM {$t = Atom.mk(null, $ATOM.text);} 
    | LPAR e=expr expr_list RPAR
      { $t = $expr_list.a;
        $e.t.setNext($expr_list.a.getFirst());
        $expr_list.a.setFirst($e.t);}
    | LPAR FORALL atom_list COMMA e=expr RPAR
      {$t = Forall.mk(null, $atom_list.a, $e.t);}
    ;
expr_list returns [Application a]: 
           expr list=expr_list {$a = $list.a;
                                $expr.t.setNext($a.getFirst());
                                $a.setFirst($expr.t);} 
         | {$a  = Application.mk((Term)null, (Term) null);};

atom_list returns [Atom a]: 
           ATOM list=atom_list {$a = Atom.mk($list.a, $ATOM.text);} 
         | ATOM {$a = Atom.mk(null, $ATOM.text);} 
         ;
    



//Lexer part

WHITESPACE  :  (' '|'\n'|'\r'|'\t')+  {$channel=HIDDEN;} 
            ;

LPAR: '('  ;
RPAR: ')' ;
DOC: '[' .* ']'{setText($text.substring(1, $text.length() - 1));};
COLON: ':';
FORALL: 'forall';
COMMA: ',';

COMMENT: '{' .* '}'{$channel=HIDDEN;};
//Identifier
ATOM : (ALPHANUMERIC | UNDERSCORE | DASH | '\'' | SYMBOL )+;      
fragment
UNDERSCORE:  '_' ;
fragment
DASH:  '-';
fragment
SYMBOL: '~'
      | '>' | '<' | '=' | '+' | '*' | '/' | '\\';
                    
fragment 
ALPHANUMERIC :  ALPHA | DIGIT ;
      
fragment 
DIGIT  :  '0'..'9' 
       ;
  
fragment 
ALPHA  : LOWER | UPPER 
       ;
                
fragment 
LOWER  : 'a'..'z' 
       ;
                
fragment 
UPPER  : 'A'..'Z' 
       ;
