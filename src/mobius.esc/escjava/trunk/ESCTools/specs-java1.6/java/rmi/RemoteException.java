package java.rmi;

public class RemoteException extends java.io.IOException {
    private static final long serialVersionUID = -5148567311918794206L;
    public Throwable detail;
    
    public RemoteException() {
        
        initCause(null);
    }
    
    public RemoteException(String s) {
        super(s);
        initCause(null);
    }
    
    public RemoteException(String s, Throwable cause) {
        super(s);
        initCause(null);
        detail = cause;
    }
    
    public String getMessage() {
        if (detail == null) {
            return super.getMessage();
        } else {
            return super.getMessage() + "; nested exception is: \n\t" + detail.toString();
        }
    }
    
    public Throwable getCause() {
        return detail;
    }
}
