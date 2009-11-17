package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.*;
import java.io.Serializable;
import javax.swing.plaf.*;
import javax.swing.plaf.basic.*;
import javax.swing.event.*;
import javax.accessibility.*;

class JMenuItem$MenuItemFocusListener implements FocusListener, Serializable {
    
    /*synthetic*/ JMenuItem$MenuItemFocusListener(javax.swing.JMenuItem$1 x0) {
        this();
    }
    
    private JMenuItem$MenuItemFocusListener() {
        
    }
    
    public void focusGained(FocusEvent event) {
    }
    
    public void focusLost(FocusEvent event) {
        JMenuItem mi = (JMenuItem)(JMenuItem)event.getSource();
        if (mi.isFocusPainted()) {
            mi.repaint();
        }
    }
}
