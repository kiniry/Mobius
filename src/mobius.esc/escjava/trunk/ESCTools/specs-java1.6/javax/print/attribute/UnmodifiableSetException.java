package javax.print.attribute;

public class UnmodifiableSetException extends RuntimeException {
    
    public UnmodifiableSetException() {
        
    }
    
    public UnmodifiableSetException(String message) {
        super(message);
    }
}
