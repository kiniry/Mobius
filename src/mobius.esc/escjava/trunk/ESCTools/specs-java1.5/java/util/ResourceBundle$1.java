package java.util;

class ResourceBundle$1 implements java.security.PrivilegedAction {
    /*synthetic*/ final String val$resName;
    /*synthetic*/ final ClassLoader val$loader;
    
    ResourceBundle$1(/*synthetic*/ final ClassLoader val$loader, /*synthetic*/ final String val$resName) {
        this.val$loader = val$loader;
        this.val$resName = val$resName;
        
    }
    
    public Object run() {
        if (val$loader != null) {
            return val$loader.getResourceAsStream(val$resName);
        } else {
            return ClassLoader.getSystemResourceAsStream(val$resName);
        }
    }
}
