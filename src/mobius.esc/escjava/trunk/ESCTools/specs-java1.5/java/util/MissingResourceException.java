package java.util;

public class MissingResourceException extends RuntimeException {
    
    public MissingResourceException(String s, String className, String key) {
        super(s);
        this.className = className;
        this.key = key;
    }
    
    public String getClassName() {
        return className;
    }
    
    public String getKey() {
        return key;
    }
    private String className;
    private String key;
}
