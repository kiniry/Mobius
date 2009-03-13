
grammar CLO;

options {
  superClass=AbstractParser;
}

@header {
  package ie.ucd.clops.dsl.parser; 
  
  import ie.ucd.clops.dsl.structs.*;
  import ie.ucd.clops.dsl.OptionTypeFactory;
  import ie.ucd.clops.dsl.OptionType;
  import ie.ucd.clops.dsl.UnknownOptionTypeException;
  import ie.ucd.clops.dsl.parser.DSLParseException;
}

@lexer::header {
  package ie.ucd.clops.dsl.parser;
}

@lexer::members {
  boolean curliesInJavaMode = false;
}

@members {
  // Nothing now.
}

/**********************************************  
 ##############################################
 ###   Parser...                            ###
 ##############################################
 **********************************************/

prog  :  clo_specification EOF         
      ;

clo_specification  :  name_section
                      (package_section)?
                      args_section
                      args_format_section
                      where_section
                      (fly_section)?
                      (overrides_section)?
                      (validity_section)?
                   ;

/**********************************************/

name_section  :  SECTION_NAME NAME
                 { getDslInformation().setParserName($NAME.text); }
              ;

/**********************************************/

package_section  :  SECTION_PACKAGE package_name
                    { getDslInformation().setPackageName($package_name.text); }
              ;
              
package_name  :  NAME ('.' NAME)*
              ;


/**********************************************/

args_section  :  SECTION_ARGS (arg_definition)+
              ;

//Currently allowing anything for the 
arg_definition  
@init { OptionDescription option = new BasicOptionDescription(); }
                :  id=arg_name
                   { option.setId($id.text); } 
                   ':' '{'
                   ( 
                     a1=arg_regexp 
                     { option.addPrefixRegexp($a1.text); }
                     (',' a=arg_regexp
                      { option.addPrefixRegexp($a.text); }
                     )* 
                   )?
                   '}'
                   (
                   ( ':' '{' t=NAME '}'
                       { try { OptionType optionType = getOptionTypeFactory().getOptionType($t.text); option.setType(optionType);
                             } catch(UnknownOptionTypeException e) { throw new DSLParseException(e.getMessage()); } 
                       }
                   )
                   |
                       { OptionType optionType = getOptionTypeFactory().getDefaultOptionType(); option.setType(optionType); }
                   ) 
                   ( ':' '['
                     pn1=property_name  
                     ( '=' pv1=property_value
                       { option.setProperty($pn1.text, $pv1.text); }
                      |
                       { option.setProperty($pn1.text, "true"); }
                     )
                     ( ','? pn=property_name 
                       ( '=' pv=property_value
                         { option.setProperty($pn.text, $pv.text); }
                        |
                         { option.setProperty($pn.text, "true"); }
                       ) 
                     )*
                     ']' 
                   )?
                   ( ':' s=option_comment
                     { option.setDescription($s.text); }
                   
                   )?
                     
                   { getDslInformation().addOptionDescription(option); }
                ;
                catch [DSLParseException e] {
                  setCustomErrorMessage(e.toString());
                  throw new RecognitionException();
                } 
                catch [RecognitionException re] {
                  reportError(re);
                  recover(input,re);
                }

arg_name  :  NAME
          ;

arg_regexp  :  STRING_CONSTANT
            ;
           
property_name  :  NAME
               ;
               
property_value  :  STRING_CONSTANT
                ;
                
option_comment  :  STRING_CONSTANT
                ;

/**********************************************/

args_format_section  :  SECTION_FORMAT format_clause  
                        { getDslInformation().setFormatString($format_clause.text); }
                        ';'
                     ;

format_clause  :  format_subclause
               ;

format_subclause  :  (   NAME  
                       | ( '(' format_subclause ')' )
                     ) 
                     (repetition_operator)?
                     (or_format_subclause)?
                  ;

or_format_subclause  :  ('|')? format_subclause
                     ;

repetition_operator  : '*' | '+' | '?'
                    ;


/**********************************************/

where_section  :  SECTION_WHERE (where_clause)*
               ;

where_clause  :  group=NAME
                 { OptionGroupDescription opGroup = new OptionGroupDescription($group.text); } 
                 ':' child1=NAME
                 { opGroup.addChild($child1.text); }  
                 (('OR'|'|') child=NAME { opGroup.addChild($child.text); } )* 
                 { getDslInformation().addOptionGroupDescription(opGroup); }
                 ';'
              ;

/**********************************************/

fly_section  :  SECTION_FLY (fly_rule)*
             ;

fly_rule  :  t=NAME
             { FlyRuleDescription or = new FlyRuleDescription($t.text); } 
             (
               condition
               { or.setConditionText($condition.text); }
             )?
             '->' n1=NAME ':=' v1=assignment_rhs
             { or.addAssignment(new AssignmentDescription($n1.text, $v1.text)); } 
             (',' 
              n=NAME ':=' v=assignment_rhs
              { or.addAssignment(new AssignmentDescription($n.text, $v.text)); }
             )* ';'
             { getDslInformation().addFlyRuleDescription(or); }
          ;
          
condition  :  UNCHECKED_CODE_BLOCK
           ;
          
assignment_rhs  :  UNCHECKED_CODE_BLOCK
                ;


/**********************************************/

overrides_section  :  SECTION_OVERRIDES (override_rule)*
                   ;

override_rule  :  condition '->' 
                  { OverrideRuleDescription ord = new OverrideRuleDescription(); 
                    ord.setConditionText($condition.text);                            } 
                  n1=NAME ':=' v1=assignment_rhs
                  { ord.addAssignment(new AssignmentDescription($n1.text, $v1.text)); } 
                  (',' 
                    n=NAME ':=' v=assignment_rhs
                    { ord.addAssignment(new AssignmentDescription($n.text, $v.text)); }
                  )* 
                  { getDslInformation().addOverrideRuleDescription(ord); }
                  ';'
               ;

/**********************************************/

validity_section  :  SECTION_VALIDITY (validity_rule)*
                  ;

validity_rule  :   standard_validity_rule
                 | requires_validity_rule
                 | exclusive_validity_rule
               ;

standard_validity_rule  :  condition
                           { ValidityRuleDescription vrd = new ValidityRuleDescription(); 
                             vrd.setConditionText($condition.text);                            }
                           ( ':' explanation
                             { vrd.setExplanation($explanation.text); }
                           )? 
                           { getDslInformation().addValidityRuleDescription(vrd); } 
                           ';'
                        ;

requires_validity_rule  :  'requires' ':' arg_name '=>' requires_expression
                           { ValidityRuleDescription vrd = ValidityRuleDescription.fromRequires($arg_name.text, $requires_expression.text); }
                           ( ':' explanation
                            { vrd.setExplanation($explanation.text); }
                           )?
                           { getDslInformation().addValidityRuleDescription(vrd); }
                           ';'
                        ;

requires_expression  :   requires_or_expression
                     ;
                     
requires_or_expression  :  requires_and_expression ( '||' requires_and_expression )*
                        ;
                        
requires_and_expression  :  requires_expression_unit ( '&&' requires_expression_unit )*
                         ;
                         
requires_expression_unit  :    arg_name 
                             | ( '(' requires_expression ')' )
                          ;

                     
exclusive_validity_rule  :  'exclusive' ':' a1=arg_name
                               { List<String> args = new java.util.LinkedList<String>();
                                 args.add($a1.text);                                    }
                               ( ',' a=arg_name 
                                 { args.add($a.text); }
                               )+
                               { ValidityRuleDescription vrd = ValidityRuleDescription.fromXOR(args); }
                               (
                                ':' explanation
                                { vrd.setExplanation($explanation.text); }
                               )?
                                { getDslInformation().addValidityRuleDescription(vrd); }
                               ';'
                            ;
               
explanation  :  STRING_CONSTANT
             ;

/**********************************************
 **********************************************/

constant  :    boolean_constant
             | integer_constant  
             | STRING_CONSTANT
             | unspecified_constant
          ;

boolean_constant  :  'true' | 'false'
                  ;

integer_constant  :  INTEGER
                  ;

unspecified_constant  :  '?'
                      ;

/**********************************************/

comparison_op  :    '='
                  | '!='
                  | '>'
                  | '<'
                  | '<='
                  | '>='
               ;


/**********************************************  
 ##############################################
 ###   Lexer...                             ###
 ##############################################
 **********************************************/ 

SECTION_NAME: 'NAME::';
SECTION_PACKAGE: 'PACKAGE::';
SECTION_ARGS: 'ARGS::' {curliesInJavaMode=false;};
SECTION_FORMAT: 'FORMAT::';
SECTION_WHERE: 'WHERE::';
SECTION_FLY: 'FLY::' {curliesInJavaMode=true;};
SECTION_OVERRIDES: 'OVERRIDES::' {curliesInJavaMode=true;};
SECTION_VALIDITY: 'VALIDITY::' {curliesInJavaMode=true;};

UNCHECKED_CODE_BLOCK  :
  {curliesInJavaMode}?=>
  UNCHECKED_CODE { setText($text.substring(1, $text.length()-1).trim()); }
  ;
   
fragment                  
UNCHECKED_CODE :
	'{' 
	(	options {greedy=false; k=2;}
	:	UNCHECKED_CODE
	|	SINGLE_LINE_COMMENT
	|	MULTI_LINE_COMMENT
	|	.
	)*
	'}'
	
   ;

STRING_CONSTANT : '"' .* '"' 
  { /* FIXME */ 
    setText($text.substring(1, $text.length() - 1));
  }
                ;

MULTI_LINE_COMMENT  :  '/*' .* '*/' { $channel=HIDDEN; }
                    ;

SINGLE_LINE_COMMENT  :  '//' .* NEWLINE  { $channel=HIDDEN; }
                     ;

fragment
NEWLINE  :  '\r'? '\n' 
         ;

/**********************************************/

//  : DIGIT  ( ALPHANUMERIC | UNDERSCORE | DASH )*
//                   ;

//Identifier name
NAME  : ALPHA ( ALPHANUMERIC | UNDERSCORE | DASH )*
      ;
                                    
fragment 
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

/**********************************************  
 ***   Whitespace                           ***
 **********************************************/
 
WHITESPACE  :  (' '|'\n'|'\r'|'\t')+ {$channel=HIDDEN;}
            ;
