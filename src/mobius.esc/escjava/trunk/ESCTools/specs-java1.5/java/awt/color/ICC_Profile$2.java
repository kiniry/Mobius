package java.awt.color;

import java.io.IOException;
import java.security.PrivilegedAction;

class ICC_Profile$2 implements PrivilegedAction {
    /*synthetic*/ final String val$name;
    
    ICC_Profile$2(/*synthetic*/ final String val$name) {
        this.val$name = val$name;
        
    }
    
    public Object run() {
        ICC_Profile p = null;
        try {
            p = ICC_Profile.getInstance(val$name);
        } catch (IOException ex) {
            throw new IllegalArgumentException("Can\'t load standard profile: " + val$name);
        }
        return p;
    }
}
