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

class JTable$8 implements Runnable {
    /*synthetic*/ final JTable this$0;
    /*synthetic*/ final WindowAdapter val$closeListener;
    /*synthetic*/ final JDialog val$abortDialog;
    /*synthetic*/ final Object val$lock;
    /*synthetic*/ final PrintRequestAttributeSet val$copyAttr;
    /*synthetic*/ final PrinterJob val$job;
    
    JTable$8(/*synthetic*/ final JTable this$0, /*synthetic*/ final PrinterJob val$job, /*synthetic*/ final PrintRequestAttributeSet val$copyAttr, /*synthetic*/ final Object val$lock, /*synthetic*/ final JDialog val$abortDialog, /*synthetic*/ final WindowAdapter val$closeListener) {
        this.this$0 = this$0;
        this.val$job = val$job;
        this.val$copyAttr = val$copyAttr;
        this.val$lock = val$lock;
        this.val$abortDialog = val$abortDialog;
        this.val$closeListener = val$closeListener;
        
    }
    
    public void run() {
        try {
            val$job.print(val$copyAttr);
        } catch (Throwable t) {
            synchronized (val$lock) {
                JTable.access$002(this$0, t);
            }
        } finally {
            SwingUtilities.invokeLater(new JTable$8$1(this));
        }
    }
}
