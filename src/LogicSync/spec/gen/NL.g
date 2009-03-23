
grammar NL;

@header {
  package mobius.logic.lang.nat.parser; 
  
  import java.util.LinkedList;
  import java.util.List;
  
  import mobius.logic.lang.nat.ast.*;
  import mobius.logic.lang.ast.FileLocation;
}

@lexer::header {
  package mobius.logic.lang.nat.parser;
}

@parser::members {
  public String fileName = null; // the file being processed
  private FileLocation tokLoc(Token t) {
    return new FileLocation(fileName,t.getLine(),t.getCharPositionInLine()+1);
  }
}

/**********************************************  
 ##############################################
 ###   Parser...                            ###
 ##############################################
 **********************************************/

 program returns [Program prog]:
   { List<Logic> list = new LinkedList<Logic>(); }
   ( logic
     { list.add($logic.v); } 
   )+
   EOF
   { $prog = Program.mk(list); }
 ;
 
 logic returns [Logic v]:
   l='logic' NAME items 'end'
   { $v = Logic.mk($NAME.text,$items.list,tokLoc($l)); }
 ;
 
 items returns [List<Item> list]:
   { List<Item> items = new LinkedList<Item>(); }
   ( item { items.add($item.v); } )+
   { $list = items; }
 ;
 
 item returns [Item v]:
   NAME ':' STRING_CONSTANT
   { $v = Item.mk($NAME.text, $STRING_CONSTANT.text, tokLoc($NAME)); }
 ;
 
/**********************************************  
 ##############################################
 ###   Lexer...                             ###
 ##############################################
 **********************************************/ 
 
STRING_CONSTANT : '"' .* '"'; 
 
 //Identifier name
NAME  : ALPHA ( ALPHANUMERIC | UNDERSCORE | DASH | '\'')*
      ;
        
UNDERSCORE  :  '_' 
            ;

DASH  :  '-'
      ;
                    
fragment 
ALPHANUMERIC  :  ALPHA | DIGIT 
              ;
               
INTEGER  :  (DIGIT)+ 
         ;
         
REAL  :  DIGIT+ '.' DIGIT+ 
      ;
      
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
       
WHITESPACE  :  (' '|'\n'|'\r'|'\t')+ {$channel=HIDDEN;}
            ;