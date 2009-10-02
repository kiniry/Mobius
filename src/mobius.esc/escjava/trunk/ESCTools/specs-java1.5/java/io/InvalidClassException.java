package java.io;

public class InvalidClassException extends ObjectStreamException {
    public String classname;
    
    public InvalidClassException(String reason) {
        super(reason);
    }
    
    public InvalidClassException(String cname, String reason) {
        super(reason);
        classname = cname;
    }
    
    public String getMessage() {
        if (classname == null) return super.getMessage(); else return classname + "; " + super.getMessage();
    }
}
