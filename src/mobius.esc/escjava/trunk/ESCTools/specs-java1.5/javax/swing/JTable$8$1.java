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

class JTable$8$1 implements Runnable {
    /*synthetic*/ final JTable$8 this$1;
    
    JTable$8$1(/*synthetic*/ final JTable$8 this$1) {
        this.this$1 = this$1;
        
    }
    
    public void run() {
        this$1.val$abortDialog.removeWindowListener(this$1.val$closeListener);
        this$1.val$abortDialog.dispose();
    }
}
