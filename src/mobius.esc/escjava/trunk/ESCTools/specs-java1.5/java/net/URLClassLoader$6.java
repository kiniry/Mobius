package java.net;

import java.net.URL;
import java.security.PrivilegedAction;

class URLClassLoader$6 implements PrivilegedAction {
    /*synthetic*/ final URL[] val$urls;
    
    URLClassLoader$6(/*synthetic*/ final URL[] val$urls) {
        this.val$urls = val$urls;
        
    }
    
    public Object run() {
        return new FactoryURLClassLoader(val$urls);
    }
}
