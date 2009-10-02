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

class JTable$6 extends AbstractAction {
    /*synthetic*/ final JTable this$0;
    /*synthetic*/ final PrinterJob val$job;
    /*synthetic*/ final JTable$ThreadSafePrintable val$wrappedPrintable;
    /*synthetic*/ final JLabel val$statusLabel;
    /*synthetic*/ final JDialog val$abortDialog;
    /*synthetic*/ final JButton val$abortButton;
    
    JTable$6(/*synthetic*/ final JTable this$0, /*synthetic*/ final JButton val$abortButton, /*synthetic*/ final JDialog val$abortDialog, /*synthetic*/ final JLabel val$statusLabel, /*synthetic*/ final JTable$ThreadSafePrintable val$wrappedPrintable, /*synthetic*/ final PrinterJob val$job) {
        this.this$0 = this$0;
        this.val$abortButton = val$abortButton;
        this.val$abortDialog = val$abortDialog;
        this.val$statusLabel = val$statusLabel;
        this.val$wrappedPrintable = val$wrappedPrintable;
        this.val$job = val$job;
        
    }
    boolean isAborted = false;
    
    public void actionPerformed(ActionEvent ae) {
        if (!isAborted) {
            isAborted = true;
            val$abortButton.setEnabled(false);
            val$abortDialog.setTitle(UIManager.getString("PrintingDialog.titleAbortingText"));
            val$statusLabel.setText(UIManager.getString("PrintingDialog.contentAbortingText"));
            val$wrappedPrintable.stopUpdatingStatus();
            val$job.cancel();
        }
    }
}
