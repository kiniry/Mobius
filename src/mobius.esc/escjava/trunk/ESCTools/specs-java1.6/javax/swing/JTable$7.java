package javax.swing;

import java.util.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.print.*;
import java.beans.*;
import javax.accessibility.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.table.*;
import javax.swing.border.*;
import javax.print.attribute.*;

class JTable$7 extends WindowAdapter {
    /*synthetic*/ final JTable this$0;
    /*synthetic*/ final Action val$abortAction;
    
    JTable$7(/*synthetic*/ final JTable this$0, /*synthetic*/ final Action val$abortAction) {
        this.this$0 = this$0;
        this.val$abortAction = val$abortAction;
        
    }
    
    public void windowClosing(WindowEvent we) {
        val$abortAction.actionPerformed(null);
    }
}
