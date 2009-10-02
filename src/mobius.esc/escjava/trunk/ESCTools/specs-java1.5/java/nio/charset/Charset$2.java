package java.nio.charset;

import java.nio.charset.spi.CharsetProvider;
import java.security.PrivilegedAction;
import java.util.Iterator;

class Charset$2 implements PrivilegedAction {
    /*synthetic*/ final String val$charsetName;
    
    Charset$2(/*synthetic*/ final String val$charsetName) {
        this.val$charsetName = val$charsetName;
        
    }
    
    public Object run() {
        for (Iterator i = Charset.access$000(); i.hasNext(); ) {
            CharsetProvider cp = (CharsetProvider)(CharsetProvider)i.next();
            Charset cs = cp.charsetForName(val$charsetName);
            if (cs != null) return cs;
        }
        return null;
    }
}
