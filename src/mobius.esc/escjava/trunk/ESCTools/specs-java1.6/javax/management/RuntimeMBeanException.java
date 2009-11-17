package javax.management;

public class RuntimeMBeanException extends JMRuntimeException {
    private static final long serialVersionUID = 5274912751982730171L;
    private java.lang.RuntimeException runtimeException;
    
    public RuntimeMBeanException(java.lang.RuntimeException e) {
        
        runtimeException = e;
    }
    
    public RuntimeMBeanException(java.lang.RuntimeException e, String message) {
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
