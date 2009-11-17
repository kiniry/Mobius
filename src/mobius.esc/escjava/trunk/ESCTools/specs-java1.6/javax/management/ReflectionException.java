package javax.management;

public class ReflectionException extends JMException {
    private static final long serialVersionUID = 9170809325636915553L;
    private java.lang.Exception exception;
    
    public ReflectionException(java.lang.Exception e) {
        
        exception = e;
    }
    
    public ReflectionException(java.lang.Exception e, String message) {
        super(message);
        exception = e;
    }
    
    public java.lang.Exception getTargetException() {
        return exception;
    }
    
    public Throwable getCause() {
        return exception;
    }
}
