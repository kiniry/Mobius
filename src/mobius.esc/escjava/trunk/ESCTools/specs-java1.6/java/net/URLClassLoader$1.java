package java.net;

import java.io.IOException;
import java.security.PrivilegedExceptionAction;
import sun.misc.Resource;

class URLClassLoader$1 implements PrivilegedExceptionAction {
    /*synthetic*/ final URLClassLoader this$0;
    /*synthetic*/ final String val$name;
    
    URLClassLoader$1(/*synthetic*/ final URLClassLoader this$0, /*synthetic*/ final String val$name) throws ClassNotFoundException {
        this.this$0 = this$0;
        this.val$name = val$name;
        
    }
    
    public Object run() throws ClassNotFoundException {
        String path = val$name.replace('.', '/').concat(".class");
        Resource res = URLClassLoader.access$000(this$0).getResource(path, false);
        if (res != null) {
            try {
                return URLClassLoader.access$100(this$0, val$name, res);
            } catch (IOException e) {
                throw new ClassNotFoundException(val$name, e);
            }
        } else {
            throw new ClassNotFoundException(val$name);
        }
    }
}
