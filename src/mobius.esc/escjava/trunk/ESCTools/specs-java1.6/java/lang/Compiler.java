package java.lang;

public final class Compiler {
    
    /*synthetic*/ static void access$000() {
        initialize();
    }
    
    private Compiler() {
        
    }
    
    private static native void initialize();
    
    private static native void registerNatives();
    static {
        registerNatives();
        java.security.AccessController.doPrivileged(new Compiler$1());
    }
    
    public static native boolean compileClass(Class clazz);
    
    public static native boolean compileClasses(String string);
    
    public static native Object command(Object any);
    
    public static native void enable();
    
    public static native void disable();
}
