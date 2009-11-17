package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.plaf.basic.*;
import javax.swing.border.*;
import java.awt.event.*;
import java.awt.AWTEvent;
import java.awt.Toolkit;
import java.util.*;

class BasicPopupMenuUI$MouseGrabber$1 implements java.security.PrivilegedAction {
    /*synthetic*/ final BasicPopupMenuUI$MouseGrabber this$0;
    
    BasicPopupMenuUI$MouseGrabber$1(/*synthetic*/ final BasicPopupMenuUI$MouseGrabber this$0) {
        this.this$0 = this$0;
        
    }
    
    public Object run() {
        Toolkit.getDefaultToolkit().addAWTEventListener(this$0, AWTEvent.MOUSE_EVENT_MASK | AWTEvent.MOUSE_MOTION_EVENT_MASK | AWTEvent.MOUSE_WHEEL_EVENT_MASK);
        return null;
    }
}
