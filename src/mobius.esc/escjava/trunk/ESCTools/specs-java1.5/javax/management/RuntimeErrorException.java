package javax.management;

public class RuntimeErrorException extends JMRuntimeException {
    private static final long serialVersionUID = 704338937753949796L;
    private java.lang.Error error;
    
    public RuntimeErrorException(java.lang.Error e) {
        
        error = e;
    }
    
    public RuntimeErrorException(java.lang.Error e, String message) {
        super(message);
        error = e;
    }
    
    public java.lang.Error getTargetError() {
        return error;
    }
    
    public Throwable getCause() {
        return error;
    }
}
