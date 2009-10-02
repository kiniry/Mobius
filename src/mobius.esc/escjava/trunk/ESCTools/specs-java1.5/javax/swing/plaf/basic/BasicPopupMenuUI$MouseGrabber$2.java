package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.plaf.basic.*;
import javax.swing.border.*;
import java.awt.event.*;
import java.awt.Toolkit;
import java.util.*;

class BasicPopupMenuUI$MouseGrabber$2 implements java.security.PrivilegedAction {
    /*synthetic*/ final BasicPopupMenuUI$MouseGrabber this$0;
    
    BasicPopupMenuUI$MouseGrabber$2(/*synthetic*/ final BasicPopupMenuUI$MouseGrabber this$0) {
        this.this$0 = this$0;
        
    }
    
    public Object run() {
        Toolkit.getDefaultToolkit().removeAWTEventListener(this$0);
        return null;
    }
}
