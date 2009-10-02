package java.io;

public abstract class ObjectStreamException extends IOException {
    
    protected ObjectStreamException(String classname) {
        super(classname);
    }
    
    protected ObjectStreamException() {
        
    }
}
