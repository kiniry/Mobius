package java.lang.reflect;

import java.security.AccessController;
import sun.reflect.ReflectionFactory;

public class Modifier {
    
    public Modifier() {
        
    }
    static {
        sun.reflect.ReflectionFactory factory = (sun.reflect.ReflectionFactory)(ReflectionFactory)AccessController.doPrivileged(new ReflectionFactory$GetReflectionFactoryAction());
        factory.setLangReflectAccess(new java.lang.reflect.ReflectAccess());
    }
    
    public static boolean isPublic(int mod) {
        return (mod & PUBLIC) != 0;
    }
    
    public static boolean isPrivate(int mod) {
        return (mod & PRIVATE) != 0;
    }
    
    public static boolean isProtected(int mod) {
        return (mod & PROTECTED) != 0;
    }
    
    public static boolean isStatic(int mod) {
        return (mod & STATIC) != 0;
    }
    
    public static boolean isFinal(int mod) {
        return (mod & FINAL) != 0;
    }
    
    public static boolean isSynchronized(int mod) {
        return (mod & SYNCHRONIZED) != 0;
    }
    
    public static boolean isVolatile(int mod) {
        return (mod & VOLATILE) != 0;
    }
    
    public static boolean isTransient(int mod) {
        return (mod & TRANSIENT) != 0;
    }
    
    public static boolean isNative(int mod) {
        return (mod & NATIVE) != 0;
    }
    
    public static boolean isInterface(int mod) {
        return (mod & INTERFACE) != 0;
    }
    
    public static boolean isAbstract(int mod) {
        return (mod & ABSTRACT) != 0;
    }
    
    public static boolean isStrict(int mod) {
        return (mod & STRICT) != 0;
    }
    
    public static String toString(int mod) {
        StringBuffer sb = new StringBuffer();
        int len;
        if ((mod & PUBLIC) != 0) sb.append("public ");
        if ((mod & PROTECTED) != 0) sb.append("protected ");
        if ((mod & PRIVATE) != 0) sb.append("private ");
        if ((mod & ABSTRACT) != 0) sb.append("abstract ");
        if ((mod & STATIC) != 0) sb.append("static ");
        if ((mod & FINAL) != 0) sb.append("final ");
        if ((mod & TRANSIENT) != 0) sb.append("transient ");
        if ((mod & VOLATILE) != 0) sb.append("volatile ");
        if ((mod & SYNCHRONIZED) != 0) sb.append("synchronized ");
        if ((mod & NATIVE) != 0) sb.append("native ");
        if ((mod & STRICT) != 0) sb.append("strictfp ");
        if ((mod & INTERFACE) != 0) sb.append("interface ");
        if ((len = sb.length()) > 0) return sb.toString().substring(0, len - 1);
        return "";
    }
    public static final int PUBLIC = 1;
    public static final int PRIVATE = 2;
    public static final int PROTECTED = 4;
    public static final int STATIC = 8;
    public static final int FINAL = 16;
    public static final int SYNCHRONIZED = 32;
    public static final int VOLATILE = 64;
    public static final int TRANSIENT = 128;
    public static final int NATIVE = 256;
    public static final int INTERFACE = 512;
    public static final int ABSTRACT = 1024;
    public static final int STRICT = 2048;
    static final int BRIDGE = 64;
    static final int VARARGS = 128;
    static final int SYNTHETIC = 4096;
    static final int ANNOTATION = 8192;
    static final int ENUM = 16384;
    
    static boolean isSynthetic(int mod) {
        return (mod & SYNTHETIC) != 0;
    }
}
