package java.io;

public class NotSerializableException extends ObjectStreamException {
    
    public NotSerializableException(String classname) {
        super(classname);
    }
    
    public NotSerializableException() {
        
    }
}
