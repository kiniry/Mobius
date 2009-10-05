package java.net;

import java.net.URL;
import java.util.Enumeration;
import java.util.NoSuchElementException;
import java.security.AccessController;

class URLClassLoader$3 implements Enumeration {
    /*synthetic*/ final URLClassLoader this$0;
    /*synthetic*/ final Enumeration val$e;
    
    URLClassLoader$3(/*synthetic*/ final URLClassLoader this$0, /*synthetic*/ final Enumeration val$e) {
        this.this$0 = this$0;
        this.val$e = val$e;
        
    }
    private URL url = null;
    
    private boolean next() {
        if (url != null) {
            return true;
        }
        do {
            URL u = (URL)(URL)AccessController.doPrivileged(new URLClassLoader$3$1(this), URLClassLoader.access$200(this$0));
            if (u == null) break;
            url = URLClassLoader.access$000(this$0).checkURL(u);
        }         while (url == null);
        return url != null;
    }
    
    public URL nextElement() {
        if (!next()) {
            throw new NoSuchElementException();
        }
        URL u = url;
        url = null;
        return u;
    }
    
    public boolean hasMoreElements() {
        return next();
    }
    
    /*synthetic public Object nextElement() {
        return this.nextElement();
    } */
}
