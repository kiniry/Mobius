package cvc3;

import java.util.*;

public class Type extends Embedded {
    // jni methods
    private static native boolean
	jniIsNull(Object Type) throws Cvc3Exception;
    private static native boolean
	jniIsBool(Object Type) throws Cvc3Exception;
    private static native boolean
	jniIsSubtype(Object Type) throws Cvc3Exception;
    private static native boolean
	jniIsFunction(Object Type) throws Cvc3Exception;

    private static native Object
	jniGetExpr(Object Type) throws Cvc3Exception;
    private static native int
	jniArity(Object Type) throws Cvc3Exception;
    private static native Type
	jniGetChild(Object Type, int i) throws Cvc3Exception;

    private static native boolean
	jniEquals(Object Type1, Object Type2) throws Cvc3Exception;
    private static native String
	jniToString(Object Type) throws Cvc3Exception;


    /// Constructor

    public Type(Object Type, EmbeddedManager embeddedManager) {
	super(Type, embeddedManager);
    }


    /// API (immutable)

    public boolean isNull() throws Cvc3Exception {
	return jniIsNull(embedded());
    }

    public boolean isBoolean() throws Cvc3Exception {
	return jniIsBool(embedded());
    }

    public boolean isSubtype() throws Cvc3Exception {
	return jniIsSubtype(embedded());
    }

    public boolean isFunction() throws Cvc3Exception {
	return jniIsFunction(embedded());
    }




    public Expr getExpr() throws Cvc3Exception {
	return new Expr(jniGetExpr(embedded()), embeddedManager());
    }

    public int arity() throws Cvc3Exception {
	return jniArity(embedded());
    }

    public Type getChild(int i) throws Cvc3Exception {
	assert(i >= 0 && i < arity());
	return new Type(jniGetChild(embedded(), i), embeddedManager());
    }


    // Printing
    public String toString() {
	String result = "";
	try {
	    result = jniToString(embedded());
	} catch (Cvc3Exception e) {
	    System.out.println(e);
	    assert(false);
	}
	return result;
    }

    public boolean equals(Object o) {
	if (this == o) return true;

	if (!(o instanceof Type)) return false;
	boolean result = false;
	try {
	    result = jniEquals(embedded(), ((Embedded)o).embedded());
	} catch (Cvc3Exception e) {
	    assert(false);
	}
	return result;
    } 

    // must return the same hash code for two exprs if equals returns true
    
    public int hashCode() {
	try {
	    return getExpr().hashCode();
	} catch (Cvc3Exception e) {
	    assert(false);
	}
	assert(false);
	return 0;
    }
}
