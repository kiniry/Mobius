package javax.xml.parsers;

public class FactoryConfigurationError extends Error {
    private Exception exception;
    
    public FactoryConfigurationError() {
        
        this.exception = null;
    }
    
    public FactoryConfigurationError(String msg) {
        super(msg);
        this.exception = null;
    }
    
    public FactoryConfigurationError(Exception e) {
        super(e.toString());
        this.exception = e;
    }
    
    public FactoryConfigurationError(Exception e, String msg) {
        super(msg);
        this.exception = e;
    }
    
    public String getMessage() {
        String message = super.getMessage();
        if (message == null && exception != null) {
            return exception.getMessage();
        }
        return message;
    }
    
    public Exception getException() {
        return exception;
    }
}
