package javax.swing.plaf.basic;

import java.awt.event.*;
import java.awt.AWTEvent;
import java.awt.Toolkit;
import java.awt.Point;
import java.io.*;
import java.security.AccessController;
import java.security.PrivilegedAction;
import java.util.*;
import java.lang.reflect.*;
import javax.sound.sampled.*;
import javax.swing.JComponent;
import javax.swing.MenuSelectionManager;
import javax.swing.MenuElement;
import javax.swing.border.*;
import javax.swing.plaf.*;

class BasicLookAndFeel$PopupInvocationHelper implements AWTEventListener, PrivilegedAction {
    /*synthetic*/ final BasicLookAndFeel this$0;
    
    BasicLookAndFeel$PopupInvocationHelper(/*synthetic*/ final BasicLookAndFeel this$0) {
        this.this$0 = this$0;
        
        AccessController.doPrivileged(this);
    }
    
    public Object run() {
        Toolkit tk = Toolkit.getDefaultToolkit();
        if (this$0.invocator == null) {
            tk.addAWTEventListener(this, AWTEvent.MOUSE_EVENT_MASK);
        } else {
            tk.removeAWTEventListener(this$0.invocator);
        }
        return null;
    }
    
    public void eventDispatched(AWTEvent ev) {
        if ((ev.getID() & AWTEvent.MOUSE_EVENT_MASK) != 0) {
            MouseEvent me = (MouseEvent)(MouseEvent)ev;
            if (me.isPopupTrigger()) {
                MenuElement[] elems = MenuSelectionManager.defaultManager().getSelectedPath();
                if (elems != null && elems.length != 0) {
                    return;
                }
                Object c = me.getSource();
                if (c instanceof JComponent) {
                    JComponent src = (JComponent)(JComponent)c;
                    if (src.getComponentPopupMenu() != null) {
                        Point pt = src.getPopupLocation(me);
                        if (pt == null) {
                            pt = me.getPoint();
                        }
                        src.getComponentPopupMenu().show(src, pt.x, pt.y);
                        me.consume();
                    }
                }
            }
        }
    }
}
