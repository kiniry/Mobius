/*
 * Created on Jul 9, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bc.io;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public interface  Code {
	//logical connectors
	public static final int TRUE = 0x00;
	public static final int FALSE = 0x01;
	public static final int AND = 0x02;
	public static final int OR = 0x03;
	public static final int IMPLIES = 0x04;
	public static final int NOT = 0x05;
	public static final int FORALL = 0x06;
	public static final int EXISTS = 0x07;
	
	// predicate symboles
	public static final int EQ = 0x10;
	public static final int GRT = 0x11;
	public static final int LESS = 0x12;
	public static final int LESSEQ = 0x13;
	public static final int GRTEQ = 0x14;
	public static final int INSTANCEOF = 0x15;
	public static final int SUBTYPE = 0x16; //<:
	public static final int NOTEQ = 0x17;
	
	//arithmetic operations
	public static final int PLUS = 0x20;
	public static final int MINUS = 0x21;
	public static final int MULT = 0x22;
	public static final int DIV = 0x23;
	public static final int REM = 0x24;
	public static final int NEG= 0x25;
	
	//bitwose operations
	public static final int BITWISEAND = 0x30;
	public static final int BITWISEOR = 0x31;
	public static final int BITWISEXOR = 0x32;
	public static final int SHL = 0x33;
	public static final int USHR = 0x34;
	public static final int SHR = 0x35;
	
	//java literals
	public static final int  INT_LITERAL = 0x40;
	public static final int CHAR_LITERAL = 0x41;
	
	//jml expressions
	public static final int TYPE_OF = 0x50; // \typeof(expr) : \TYPE
	public static final int ELEM_TYPE = 0x51; //  \elemtype(array_expr)
	public static final int RESULT = 0x52; //  \result
//	public static final int ALL_ARRAY_ELEM =  0x53; // *
	public static final int _type = 0x54; //  \type(javaType)  : \TYPE
	public static final int  TYPE = 0x55 ; //  \TYPE
	public static final int ARRAYLENGTH = 0x56;
	
	// java expressions
	public static final int METHOD_CALL = 0x60;
	public static final int ARRAY_ACCESS = 0x61;
	public static final int CAST =  0x62;
	public static final int FULL_QUALIFIED_NAME = 0x63;
	public static final int BOOLEAN_EXPR = 0x64; // ? :
	
	// references and variables 
	public static final int THIS =  0x70;
	public static final int  OLD_THIS = 0x71;
	public static final int NULL = 0x72;
	
	public static final int FIELD_LOC = 0x80;
	public static final int OLD_FIELD_REF = 0x81;
	
	public static final int LOCAL_VARIABLE = 0x90;
	public static final int OLD_LOCAL_VARIABLE = 0x91;
	
	public static final int JML_MODEL_FIELD = 0xA0; 	
	public static final int OLD_JML_MODEL_FIELD = 0xA1;
	
	public static final int METHOD_REF = 0xB0;
	
	public static final int JAVA_TYPE  = 0xC0;

	public static final int MODIFIES_EVERYTHING  = 0xD0;
	public static final int MODIFIES_NOTHING = 0xD1;
	public static final int MODIFIES_IDENT  = 0xD2;
	public static final int MODIFIES_DOT = 0xD3;
	public static final int MODIFIES_ARRAY = 0xD4;
	public static final int MODIFIES_SINGLE_INDICE = 0xD5;
	public static final int MODIFIES_INTERVAL = 0xD6;
	public static final int MODIFIES_STAR = 0xD7;		
	
	public static final int BOUND_VAR = 0xE0;		
	
	
	// virtual machine instructions
	public static final int STACK = 0xF0;
	public static final int STACK_COUNTER = 0xF1;
	
}
