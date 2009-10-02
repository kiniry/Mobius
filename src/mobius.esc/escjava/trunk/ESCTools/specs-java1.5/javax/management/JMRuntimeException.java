package javax.management;

public class JMRuntimeException extends RuntimeException {
    private static final long serialVersionUID = 6573344628407841861L;
    
    public JMRuntimeException() {
        
    }
    
    public JMRuntimeException(String message) {
        super(message);
    }
    
    JMRuntimeException(String message, Throwable cause) {
        super(message);
        try {
            java.lang.reflect.Method initCause = Throwable.class.getMethod("initCause", new Class[]{Throwable.class});
            initCause.invoke(this, new Object[]{cause});
        } catch (Exception e) {
        }
    }
}
