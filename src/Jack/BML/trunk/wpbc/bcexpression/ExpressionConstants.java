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
	public static final byte  INTERFACE_METHOD_CALL = 26;
	public static final byte  ARRAYACCESS = 2;
	public static final byte  FIELDACCESS = 3; 
	public static final byte  OBJECTACCESS = 4; 
	public static final byte  NULL = 5;
	public static final byte  PLUS = 6;
	public static final byte  MINUS = 7;
	public static final byte  MULT = 8; 
	public static final byte  DIV = 9;
	public static final byte  REM  = 10;
	public static final byte  SHL  = 11;
	public static final byte  SHR  = 12;
	public static final byte  TYPEOF = 20;
	public static final byte  ELEMTYPE = 21;
	public static final byte  OLD = 22;
	public static final byte  RESULT = 23;
	public static final byte  TYPE = 24;
	public static final byte  TYPE_EXPRESSION = 25;	// \type(expr)
	public static final byte  ALL_ARRAY_ELEM = 27; // * 
	public static final byte  ARRAY_ELEM_FROM_TO = 28;
	public static final byte  _TYPE = 29;
	public static final byte  INT_LITERAL = 30;
	public static final byte  STRING_LITERAL = 31;
	public static final byte  REFERENCE = 32;
	public static final byte  VARIABLE = 33;
	public static final byte  EXCEPTION_VARIABLE = 34;
	public static final byte  JAVA_TYPE = 35;
}
