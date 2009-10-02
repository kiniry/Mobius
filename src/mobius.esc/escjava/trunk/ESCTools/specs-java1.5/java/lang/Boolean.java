package java.lang;

public final class Boolean implements java.io.Serializable, Comparable {
    public static final Boolean TRUE = new Boolean(true);
    public static final Boolean FALSE = new Boolean(false);
    public static final Class TYPE = Class.getPrimitiveClass("boolean");
    private final boolean value;
    private static final long serialVersionUID = -3665804199014368530L;
    
    public Boolean(boolean value) {
        
        this.value = value;
    }
    
    public Boolean(String s) {
        this(toBoolean(s));
    }
    
    public static boolean parseBoolean(String s) {
        return toBoolean(s);
    }
    
    public boolean booleanValue() {
        return value;
    }
    
    public static Boolean valueOf(boolean b) {
        return (b ? TRUE : FALSE);
    }
    
    public static Boolean valueOf(String s) {
        return toBoolean(s) ? TRUE : FALSE;
    }
    
    public static String toString(boolean b) {
        return b ? "true" : "false";
    }
    
    public String toString() {
        return value ? "true" : "false";
    }
    
    public int hashCode() {
        return value ? 1231 : 1237;
    }
    
    public boolean equals(Object obj) {
        if (obj instanceof Boolean) {
            return value == ((Boolean)(Boolean)obj).booleanValue();
        }
        return false;
    }
    
    public static boolean getBoolean(String name) {
        boolean result = false;
        try {
            result = toBoolean(System.getProperty(name));
        } catch (IllegalArgumentException e) {
        } catch (NullPointerException e) {
        }
        return result;
    }
    
    public int compareTo(Boolean b) {
        return (b.value == value ? 0 : (value ? 1 : -1));
    }
    
    private static boolean toBoolean(String name) {
        return ((name != null) && name.equalsIgnoreCase("true"));
    }
    
    /*synthetic*/ public int compareTo(Object x0) {
        return this.compareTo((Boolean)x0);
    }
}
