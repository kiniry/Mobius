package javax.management;

public class MBeanException extends JMException {
    private static final long serialVersionUID = 4066342430588744142L;
    private java.lang.Exception exception;
    
    public MBeanException(java.lang.Exception e) {
        
        exception = e;
    }
    
    public MBeanException(java.lang.Exception e, String message) {
        super(message);
        exception = e;
    }
    
    public Exception getTargetException() {
        return exception;
    }
    
    public Throwable getCause() {
        return exception;
    }
}
