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
import java.text.MessageFormat;
import javax.print.attribute.*;

class JTable$ThreadSafePrintable implements Printable {
    
    /*synthetic*/ static Throwable access$602(JTable$ThreadSafePrintable x0, Throwable x1) {
        return x0.retThrowable = x1;
    }
    
    /*synthetic*/ static Printable access$500(JTable$ThreadSafePrintable x0) {
        return x0.printDelegate;
    }
    
    /*synthetic*/ static int access$402(JTable$ThreadSafePrintable x0, int x1) {
        return x0.retVal = x1;
    }
    
    /*synthetic*/ static MessageFormat access$300(JTable$ThreadSafePrintable x0) {
        return x0.statusFormat;
    }
    
    /*synthetic*/ static JLabel access$200(JTable$ThreadSafePrintable x0) {
        return x0.statusLabel;
    }
    /*synthetic*/ final JTable this$0;
    private Printable printDelegate;
    private MessageFormat statusFormat;
    private JLabel statusLabel;
    private int retVal;
    private Throwable retThrowable;
    
    public JTable$ThreadSafePrintable(/*synthetic*/ final JTable this$0, Printable printDelegate) {
        this.this$0 = this$0;
        
        this.printDelegate = printDelegate;
    }
    
    public void startUpdatingStatus(MessageFormat statusFormat, JLabel statusLabel) {
        this.statusFormat = statusFormat;
        this.statusLabel = statusLabel;
    }
    
    public void stopUpdatingStatus() {
        statusFormat = null;
        statusLabel = null;
    }
    
    public int print(final Graphics graphics, final PageFormat pageFormat, final int pageIndex) throws PrinterException {
        Runnable runnable = new JTable$ThreadSafePrintable$1(this, pageIndex, graphics, pageFormat);
        synchronized (runnable) {
            retVal = -1;
            retThrowable = null;
            SwingUtilities.invokeLater(runnable);
            while (retVal == -1 && retThrowable == null) {
                try {
                    runnable.wait();
                } catch (InterruptedException ie) {
                }
            }
            if (retThrowable != null) {
                if (retThrowable instanceof PrinterException) {
                    throw (PrinterException)(PrinterException)retThrowable;
                } else if (retThrowable instanceof RuntimeException) {
                    throw (RuntimeException)(RuntimeException)retThrowable;
                } else if (retThrowable instanceof Error) {
                    throw (Error)(Error)retThrowable;
                }
                throw new AssertionError(retThrowable);
            }
            return retVal;
        }
    }
}
