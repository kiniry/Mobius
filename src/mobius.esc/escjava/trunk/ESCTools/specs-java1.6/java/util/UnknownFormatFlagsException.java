package java.util;

public class UnknownFormatFlagsException extends IllegalFormatException {
    private static final long serialVersionUID = 19370506L;
    private String flags;
    
    public UnknownFormatFlagsException(String f) {
        
        if (f == null) throw new NullPointerException();
        this.flags = f;
    }
    
    public String getFlags() {
        return flags;
    }
    
    public String getMessage() {
        return "Flags = " + flags;
    }
}
