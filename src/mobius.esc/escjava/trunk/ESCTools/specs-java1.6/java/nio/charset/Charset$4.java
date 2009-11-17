package java.nio.charset;

import java.nio.charset.spi.CharsetProvider;
import java.security.PrivilegedAction;
import java.util.Collections;
import java.util.Iterator;
import java.util.TreeMap;
import sun.misc.ASCIICaseInsensitiveComparator;

class Charset$4 implements PrivilegedAction {
    
    Charset$4() {
        
    }
    
    public Object run() {
        TreeMap m = new TreeMap(ASCIICaseInsensitiveComparator.CASE_INSENSITIVE_ORDER);
        Charset.access$300(Charset.access$200().charsets(), m);
        for (Iterator i = Charset.access$000(); i.hasNext(); ) {
            CharsetProvider cp = (CharsetProvider)(CharsetProvider)i.next();
            Charset.access$300(cp.charsets(), m);
        }
        return Collections.unmodifiableSortedMap(m);
    }
}
