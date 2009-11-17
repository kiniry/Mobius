package java.awt;

import java.awt.event.KeyEvent;
import java.beans.*;
import java.util.logging.*;
import java.lang.reflect.*;
import java.security.PrivilegedAction;

class KeyboardFocusManager$2 implements PrivilegedAction {
    /*synthetic*/ static final boolean $assertionsDisabled = !KeyboardFocusManager.class.desiredAssertionStatus();
    
    KeyboardFocusManager$2() {
        
    }
    
    public Object run() {
        Field field = null;
        try {
            field = KeyEvent.class.getDeclaredField("isProxyActive");
            if (field != null) {
                field.setAccessible(true);
            }
        } catch (NoSuchFieldException nsf) {
            if (!$assertionsDisabled) throw new AssertionError();
        }
        return field;
    }
}
