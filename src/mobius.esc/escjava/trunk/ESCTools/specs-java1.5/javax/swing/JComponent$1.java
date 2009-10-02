package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.border.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

class JComponent$1 implements java.security.PrivilegedAction {
    
    JComponent$1() {
        
    }
    
    public Object run() {
        String value = System.getProperty("suppressSwingDropSupport");
        if (value != null) {
            return Boolean.valueOf(value);
        }
        return Boolean.FALSE;
    }
}
