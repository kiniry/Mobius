/*
 * Created on 14 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public interface ExpressionConstants {
	//public static final byte  IDENT = 0;
	public static final byte  METHOD_CALL = 1;
	public static final byte  INTERFACE_METHOD_CALL = 2;
	public static final byte  ARRAYACCESS = 3;
	public static final byte  FIELDACCESS = 4; 
	public static final byte  OBJECTACCESS = 5; 
	public static final byte  NULL = 6;
	
	//arithmetic operations
	public static final byte  ADD = 7;
	public static final byte  SUB = 8;
	public static final byte  MULT = 9; 
	public static final byte  DIV = 10;
	public static final byte  REM  = 11;
	public static final byte  NEG  = 12;
	public static final byte  NOP = 13;
	
	public static final byte  TYPEOF = 14;
	public static final byte  ELEMTYPE = 15;
	public static final byte  OLD = 16;
	public static final byte  RESULT = 17;
	public static final byte  TYPE = 18;
	public static final byte  TYPE_EXPRESSION = 19;	// \type(expr)
	public static final byte  ALL_ARRAY_ELEM = 20; // * 
	public static final byte  ARRAY_ELEM_FROM_TO = 21;
	public static final byte  _TYPE = 22;
	public static final byte  INT_LITERAL = 23;
	public static final byte  STRING_LITERAL = 24;
	public static final byte  REFERENCE = 25;
	public static final byte  VARIABLE = 26;
	public static final byte  EXCEPTION_VARIABLE = 27;
	public static final byte  JAVA_TYPE = 28;
	
	public static final byte STACK = 29;
	public static final byte STACK_COUNTER = 30;

	//bitwise expressions
	public static final byte  SHL  = 31;
	public static final byte  SHR  = 32;
	public static final byte BITWISEOR = 33;
	public static final byte BITWISEAND = 34;
	public static final byte BITWISEXOR = 35;
	
}
