package java.util;

public class IllegalFormatFlagsException extends IllegalFormatException {
    private static final long serialVersionUID = 790824L;
    private String flags;
    
    public IllegalFormatFlagsException(String f) {
        
        if (f == null) throw new NullPointerException();
        this.flags = f;
    }
    
    public String getFlags() {
        return flags;
    }
    
    public String getMessage() {
        return "Flags = \'" + flags + "\'";
    }
}
