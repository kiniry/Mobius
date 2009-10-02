package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.border.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

class JComponent$2 implements Runnable {
    /*synthetic*/ final JComponent this$0;
    
    JComponent$2(/*synthetic*/ final JComponent this$0) {
        this.this$0 = this$0;
        
    }
    
    public void run() {
        this$0.revalidate();
    }
}
