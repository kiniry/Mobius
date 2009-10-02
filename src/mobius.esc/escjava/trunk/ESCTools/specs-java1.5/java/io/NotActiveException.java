package java.io;

public class NotActiveException extends ObjectStreamException {
    
    public NotActiveException(String reason) {
        super(reason);
    }
    
    public NotActiveException() {
        
    }
}
