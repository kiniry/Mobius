package java.util.jar;

import java.util.Comparator;
import sun.misc.ASCIICaseInsensitiveComparator;

public class Attributes$Name {
    private String name;
    private int hashCode = -1;
    
    public Attributes$Name(String name) {
        
        if (name == null) {
            throw new NullPointerException("name");
        }
        if (!isValid(name)) {
            throw new IllegalArgumentException(name);
        }
        this.name = name.intern();
    }
    
    private static boolean isValid(String name) {
        int len = name.length();
        if (len > 70 || len == 0) {
            return false;
        }
        for (int i = 0; i < len; i++) {
            if (!isValid(name.charAt(i))) {
                return false;
            }
        }
        return true;
    }
    
    private static boolean isValid(char c) {
        return isAlpha(c) || isDigit(c) || c == '_' || c == '-';
    }
    
    private static boolean isAlpha(char c) {
        return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z');
    }
    
    private static boolean isDigit(char c) {
        return c >= '0' && c <= '9';
    }
    
    public boolean equals(Object o) {
        if (o instanceof Attributes$Name) {
            Comparator c = ASCIICaseInsensitiveComparator.CASE_INSENSITIVE_ORDER;
            return c.compare(name, ((Attributes$Name)(Attributes$Name)o).name) == 0;
        } else {
            return false;
        }
    }
    
    public int hashCode() {
        if (hashCode == -1) {
            hashCode = ASCIICaseInsensitiveComparator.lowerCaseHashCode(name);
        }
        return hashCode;
    }
    
    public String toString() {
        return name;
    }
    public static final Attributes$Name MANIFEST_VERSION = new Attributes$Name("Manifest-Version");
    public static final Attributes$Name SIGNATURE_VERSION = new Attributes$Name("Signature-Version");
    public static final Attributes$Name CONTENT_TYPE = new Attributes$Name("Content-Type");
    public static final Attributes$Name CLASS_PATH = new Attributes$Name("Class-Path");
    public static final Attributes$Name MAIN_CLASS = new Attributes$Name("Main-Class");
    public static final Attributes$Name SEALED = new Attributes$Name("Sealed");
    public static final Attributes$Name EXTENSION_LIST = new Attributes$Name("Extension-List");
    public static final Attributes$Name EXTENSION_NAME = new Attributes$Name("Extension-Name");
    public static final Attributes$Name EXTENSION_INSTALLATION = new Attributes$Name("Extension-Installation");
    public static final Attributes$Name IMPLEMENTATION_TITLE = new Attributes$Name("Implementation-Title");
    public static final Attributes$Name IMPLEMENTATION_VERSION = new Attributes$Name("Implementation-Version");
    public static final Attributes$Name IMPLEMENTATION_VENDOR = new Attributes$Name("Implementation-Vendor");
    public static final Attributes$Name IMPLEMENTATION_VENDOR_ID = new Attributes$Name("Implementation-Vendor-Id");
    public static final Attributes$Name IMPLEMENTATION_URL = new Attributes$Name("Implementation-URL");
    public static final Attributes$Name SPECIFICATION_TITLE = new Attributes$Name("Specification-Title");
    public static final Attributes$Name SPECIFICATION_VERSION = new Attributes$Name("Specification-Version");
    public static final Attributes$Name SPECIFICATION_VENDOR = new Attributes$Name("Specification-Vendor");
}
