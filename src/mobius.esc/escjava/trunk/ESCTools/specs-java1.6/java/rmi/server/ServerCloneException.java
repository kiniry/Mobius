package java.rmi.server;

public class ServerCloneException extends CloneNotSupportedException {
    public Exception detail;
    private static final long serialVersionUID = 6617456357664815945L;
    
    public ServerCloneException(String s) {
        super(s);
        initCause(null);
    }
    
    public ServerCloneException(String s, Exception cause) {
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
