package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.plaf.basic.*;
import javax.swing.border.*;
import java.awt.event.*;
import java.util.*;

class BasicPopupMenuUI$1 implements java.security.PrivilegedAction {
    
    BasicPopupMenuUI$1() {
        
    }
    
    public Boolean run() {
        String pKey = "sun.swing.unpostPopupsOnWindowDeactivation";
        String value = System.getProperty(pKey, "true");
        return Boolean.valueOf(value);
    }
    
    /*synthetic*/ public Object run() {
        return this.run();
    }
}
