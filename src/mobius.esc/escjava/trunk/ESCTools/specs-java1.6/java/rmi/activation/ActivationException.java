package java.rmi.activation;

public class ActivationException extends Exception {
    public Throwable detail;
    private static final long serialVersionUID = -4320118837291406071L;
    
    public ActivationException() {
        
        initCause(null);
    }
    
    public ActivationException(String s) {
        super(s);
        initCause(null);
    }
    
    public ActivationException(String s, Throwable cause) {
        super(s);
        initCause(null);
        detail = cause;
    }
    
    public String getMessage() {
        if (detail == null) return super.getMessage(); else return super.getMessage() + "; nested exception is: \n\t" + detail.toString();
    }
    
    public Throwable getCause() {
        return detail;
    }
}
