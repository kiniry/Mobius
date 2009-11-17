package javax.swing.text.html;

import java.io.InputStream;

class ResourceLoader implements java.security.PrivilegedAction {
    
    ResourceLoader(String name) {
        
        this.name = name;
    }
    
    public Object run() {
        Object o = HTMLEditorKit.class.getResourceAsStream(name);
        return o;
    }
    
    public static InputStream getResourceAsStream(String name) {
        java.security.PrivilegedAction a = new ResourceLoader(name);
        return (InputStream)(InputStream)java.security.AccessController.doPrivileged(a);
    }
    private String name;
}
