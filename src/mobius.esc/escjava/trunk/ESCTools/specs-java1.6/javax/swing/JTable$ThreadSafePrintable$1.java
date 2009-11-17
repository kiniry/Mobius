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

class JTable$ThreadSafePrintable$1 implements Runnable {
    /*synthetic*/ final JTable$ThreadSafePrintable this$1;
    /*synthetic*/ final PageFormat val$pageFormat;
    /*synthetic*/ final Graphics val$graphics;
    /*synthetic*/ final int val$pageIndex;
    
    JTable$ThreadSafePrintable$1(/*synthetic*/ final JTable$ThreadSafePrintable this$1, /*synthetic*/ final int val$pageIndex, /*synthetic*/ final Graphics val$graphics, /*synthetic*/ final PageFormat val$pageFormat) {
        this.this$1 = this$1;
        this.val$pageIndex = val$pageIndex;
        this.val$graphics = val$graphics;
        this.val$pageFormat = val$pageFormat;
        
    }
    
    public synchronized void run() {
        JTable.access$102(this$1.this$0, true);
        try {
            if (JTable.ThreadSafePrintable.access$200(this$1) != null) {
                Object[] pageNumber = new Object[]{new Integer(val$pageIndex + 1)};
                JTable.ThreadSafePrintable.access$200(this$1).setText(JTable.ThreadSafePrintable.access$300(this$1).format(pageNumber));
            }
            JTable.ThreadSafePrintable.access$402(this$1, JTable.ThreadSafePrintable.access$500(this$1).print(val$graphics, val$pageFormat, val$pageIndex));
        } catch (Throwable throwable) {
            JTable.ThreadSafePrintable.access$602(this$1, throwable);
        } finally {
            JTable.access$102(this$1.this$0, false);
            notifyAll();
        }
    }
}
