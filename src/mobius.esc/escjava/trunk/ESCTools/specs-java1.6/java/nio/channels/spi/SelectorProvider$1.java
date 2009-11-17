package java.nio.channels.spi;

import java.nio.channels.*;
import java.security.PrivilegedAction;

class SelectorProvider$1 implements PrivilegedAction {
    
    SelectorProvider$1() {
        
    }
    
    public Object run() {
        if (SelectorProvider.access$000()) return SelectorProvider.access$100();
        if (SelectorProvider.access$200()) return SelectorProvider.access$100();
        SelectorProvider.access$102(sun.nio.ch.DefaultSelectorProvider.create());
        return SelectorProvider.access$100();
    }
}
