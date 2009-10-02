package java.net;

import java.net.URL;
import java.security.PrivilegedAction;

class URLClassLoader$5 implements PrivilegedAction {
    /*synthetic*/ final ClassLoader val$parent;
    /*synthetic*/ final URL[] val$urls;
    
    URLClassLoader$5(/*synthetic*/ final URL[] val$urls, /*synthetic*/ final ClassLoader val$parent) {
        this.val$urls = val$urls;
        this.val$parent = val$parent;
        
    }
    
    public Object run() {
        return new FactoryURLClassLoader(val$urls, val$parent);
    }
}
