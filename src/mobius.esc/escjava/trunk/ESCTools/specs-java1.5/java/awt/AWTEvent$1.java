package java.awt;

import java.awt.event.*;
import java.lang.reflect.Field;

class AWTEvent$1 implements java.security.PrivilegedAction {
    
    AWTEvent$1() {
        
    }
    
    public Object run() {
        Field field = null;
        try {
            field = InputEvent.class.getDeclaredField("canAccessSystemClipboard");
            field.setAccessible(true);
            return field;
        } catch (SecurityException e) {
        } catch (NoSuchFieldException e) {
        }
        return null;
    }
}
