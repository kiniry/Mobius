package java.nio.charset.spi;

import java.nio.charset.Charset;
import java.util.Iterator;

public abstract class CharsetProvider {
    
    protected CharsetProvider() {
        
        SecurityManager sm = System.getSecurityManager();
        if (sm != null) sm.checkPermission(new RuntimePermission("charsetProvider"));
    }
    
    public abstract Iterator charsets();
    
    public abstract Charset charsetForName(String charsetName);
}
