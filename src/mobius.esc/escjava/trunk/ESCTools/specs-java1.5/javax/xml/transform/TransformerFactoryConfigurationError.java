package javax.xml.transform;

public class TransformerFactoryConfigurationError extends Error {
    private Exception exception;
    
    public TransformerFactoryConfigurationError() {
        
        this.exception = null;
    }
    
    public TransformerFactoryConfigurationError(String msg) {
        super(msg);
        this.exception = null;
    }
    
    public TransformerFactoryConfigurationError(Exception e) {
        super(e.toString());
        this.exception = e;
    }
    
    public TransformerFactoryConfigurationError(Exception e, String msg) {
        super(msg);
        this.exception = e;
    }
    
    public String getMessage() {
        String message = super.getMessage();
        if ((message == null) && (exception != null)) {
            return exception.getMessage();
        }
        return message;
    }
    
    public Exception getException() {
        return exception;
    }
}
