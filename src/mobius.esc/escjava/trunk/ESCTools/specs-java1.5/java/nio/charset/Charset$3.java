package java.nio.charset;

import java.nio.charset.spi.CharsetProvider;
import java.security.PrivilegedAction;

class Charset$3 implements PrivilegedAction {
    
    Charset$3() {
        
    }
    
    public Object run() {
        try {
            Class epc = Class.forName("sun.nio.cs.ext.ExtendedCharsets");
            Charset.access$102((CharsetProvider)(CharsetProvider)epc.newInstance());
        } catch (ClassNotFoundException x) {
        } catch (InstantiationException x) {
            throw new Error(x);
        } catch (IllegalAccessException x) {
            throw new Error(x);
        }
        return null;
    }
}
