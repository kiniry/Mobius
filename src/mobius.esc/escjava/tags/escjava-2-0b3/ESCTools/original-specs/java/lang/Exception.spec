package java.lang;

public class Exception extends java.lang.Throwable {
    static final long serialVersionUID;
    /*@ pure */ public Exception();
    /*@ pure */ public Exception(java.lang.String s);
    /*@ pure */ public Exception(java.lang.String s,java.lang.Throwable e);
    /*@ pure */ public Exception(java.lang.Throwable e);
}
