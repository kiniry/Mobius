package java.awt;

import java.util.MissingResourceException;
import java.util.ResourceBundle;
import java.awt.event.*;
import java.awt.peer.*;
import java.awt.*;

class Toolkit$3 implements java.security.PrivilegedAction {
    
    Toolkit$3() {
        
    }
    
    public Object run() {
        try {
            Toolkit.access$102(ResourceBundle.getBundle("sun.awt.resources.awt"));
        } catch (MissingResourceException e) {
        }
        return null;
    }
}
