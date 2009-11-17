package javax.management;

public class RuntimeOperationsException extends JMRuntimeException {
    private static final long serialVersionUID = -8408923047489133588L;
    private java.lang.RuntimeException runtimeException;
    
    public RuntimeOperationsException(java.lang.RuntimeException e) {
        
        runtimeException = e;
    }
    
    public RuntimeOperationsException(java.lang.RuntimeException e, String message) {
        super(message);
        runtimeException = e;
    }
    
    public java.lang.RuntimeException getTargetException() {
        return runtimeException;
    }
    
    public Throwable getCause() {
        return runtimeException;
    }
}
