package b2bpl.bytecode.attributes;


public class BMLAttributeTags {

  public static final int TRUE = 0x00;

  public static final int FALSE = 0x01;

  public static final int AND = 0x02;

  public static final int OR = 0x03;

  public static final int IMPLIES = 0x04;

  public static final int NOT = 0x05;

  public static final int FORALL = 0x06;

  public static final int EXISTS = 0x07;

  public static final int EQUALS = 0x10;

  public static final int GREATER = 0x11;

  public static final int LESS = 0x12;

  public static final int LESS_EQUAL = 0x13;

  public static final int GREATER_EQUAL = 0x14;

  public static final int INSTANCEOF = 0x15;

  public static final int SUBTYPE = 0x16;

  public static final int NOT_EQUALS = 0x17;

  public static final int PLUS = 0x20;

  public static final int MINUS = 0x21;

  public static final int TIMES = 0x22;

  public static final int DIVIDE = 0x23;

  public static final int REMAINDER = 0x24;

  public static final int UNARY_MINUS = 0x25;

  public static final int BITWISE_AND = 0x30;

  public static final int BITWISE_OR = 0x31;

  public static final int BITWISE_XOR = 0x32;

  public static final int SHL = 0x33;

  public static final int SHR = 0x34;

  public static final int USHR = 0x35;

  public static final int INT_LITERAL = 0x40;

  public static final int CHAR_LITERAL = 0x41;

  public static final int TYPE_OF = 0x50; // \typeof(expr) : \TYPE

  public static final int ELEM_TYPE = 0x51; //  \elemtype(array_expr)

  public static final int RESULT = 0x52; //  \result
  //    public static final int ALL_ARRAY_ELEM =  0x53; // *

  public static final int type = 0x54; //  \type(javaType)  : \TYPE

  public static final int TYPE = 0x55; //  \TYPE

  public static final int ARRAY_LENGTH = 0x56;

  public static final int METHOD_CALL = 0x60;

  public static final int ARRAY_ACCESS = 0x61;

  public static final int CAST = 0x62;

  public static final int FIELD_ACCESS = 0x63;

  public static final int CONDITIONAL_EXPRESSION = 0x64;

  public static final int THIS = 0x70;

  public static final int OLD_THIS = 0x71;

  public static final int NULL = 0x72;

  public static final int FIELD = 0x80;

  public static final int OLD_FIELD = 0x81;

  public static final int LOCAL_VARIABLE = 0x90;

  public static final int OLD_LOCAL_VARIABLE = 0x91;

  public static final int MODEL_FIELD = 0xA0;

  public static final int OLD_MODEL_FIELD = 0xA1;

  public static final int METHOD = 0xB0;

  public static final int JAVA_TYPE = 0xC0;

  public static final int MODIFIES_EVERYTHING = 0xD0;

  public static final int MODIFIES_NOTHING = 0xD1;

  public static final int MODIFIES_IDENT = 0xD2;

  public static final int MODIFIES_DOT = 0xD3;

  public static final int MODIFIES_ARRAY = 0xD4;

  public static final int MODIFIES_ARRAY_INDEX = 0xD5;

  public static final int MODIFIES_ARRAY_INTERVAL = 0xD6;

  public static final int MODIFIES_ARRAY_ALL = 0xD7;

  public static final int BOUND_VARIABLE = 0xE0;

  public static final int STACK_ELEMENT = 0xF0;

  public static final int STACK_COUNTER = 0xF1;

  public static final String[] NAMES = new String[255];

  static {
    NAMES[TRUE] = "true";
    NAMES[FALSE] = "false";
    NAMES[AND] = "&&";
    NAMES[OR] = "||";
    NAMES[IMPLIES] = "==>";
    NAMES[NOT] = "!";
    NAMES[FORALL] = "\\forall";
    NAMES[EXISTS] = "\\exists";
    NAMES[EQUALS] = "==";
    NAMES[GREATER] = ">";
    NAMES[LESS] = "<";
    NAMES[LESS_EQUAL] = "<=";
    NAMES[GREATER_EQUAL] = ">=";
    NAMES[INSTANCEOF] = "instanceof";
    NAMES[SUBTYPE] = "<:";
    NAMES[NOT_EQUALS] = "!=";
    NAMES[PLUS] = "+";
    NAMES[MINUS] = "-";
    NAMES[TIMES] = "*";
    NAMES[DIVIDE] = "/";
    NAMES[REMAINDER] = "%";
    NAMES[UNARY_MINUS] = "- (unary)";
    NAMES[BITWISE_AND] = "&";
    NAMES[BITWISE_OR] = "|";
    NAMES[BITWISE_XOR] = "^";
    NAMES[SHL] = "<<";
    NAMES[SHR] = ">>";
    NAMES[USHR] = ">>>";
    NAMES[INT_LITERAL] = "<int-literal>";
    NAMES[CHAR_LITERAL] = "<char-literal>";
    NAMES[TYPE_OF] = "\\typeof"; // \typeof(expr) : \TYPE
    NAMES[ELEM_TYPE] = "\\elemtype"; //  \elemtype(array_expr)
    NAMES[RESULT] = "\\result"; //  \result
    //    NAMES[ALL_ARRAY_ELEM] =  0x53; // *
    NAMES[type] = "\\type"; //  \type(javaType)  : \TYPE
    NAMES[TYPE] = "\\TYPE"; //  \TYPE
    NAMES[ARRAY_LENGTH] = "<array-length>";
    NAMES[METHOD_CALL] = "<method-call>";
    NAMES[ARRAY_ACCESS] = "<array-access>";
    NAMES[CAST] = "<cast>";
    NAMES[FIELD_ACCESS] = "<field-access>";
    NAMES[CONDITIONAL_EXPRESSION] = "? : ";
    NAMES[THIS] = "this";
    NAMES[OLD_THIS] = "\\old(this)";
    NAMES[NULL] = "null";
    NAMES[FIELD] = "<field-reference>";
    NAMES[OLD_FIELD] = "<old-field-reference>";
    NAMES[LOCAL_VARIABLE] = "<local-variable>";
    NAMES[OLD_LOCAL_VARIABLE] = "<old-local-variable>";
    NAMES[MODEL_FIELD] = "<model-field-reference>";
    NAMES[OLD_MODEL_FIELD] = "<old-model-field-reference>";
    NAMES[METHOD] = "<method-reference>";
    NAMES[JAVA_TYPE] = "<java-type>";
    NAMES[MODIFIES_EVERYTHING] = "\\everything";
    NAMES[MODIFIES_NOTHING] = "\\nothing";
    NAMES[MODIFIES_IDENT] = "<modifies-ident>";
    NAMES[MODIFIES_DOT] = "<modifies-dot>";
    NAMES[MODIFIES_ARRAY] = "<modifies-array>";
    NAMES[MODIFIES_ARRAY_INDEX] = "<modifies-array-index>";
    NAMES[MODIFIES_ARRAY_INTERVAL] = "<modifies-array-interval>";
    NAMES[MODIFIES_ARRAY_ALL] = "<modifies-array-all>";
    NAMES[BOUND_VARIABLE] = "<bound-variable>";
    NAMES[STACK_ELEMENT] = "<stack-element>";
    NAMES[STACK_COUNTER] = "<stack-counter>";
  }
}
