package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.text.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

class JTextComponent$AccessibleJTextComponent$1 extends ComponentAdapter {
    /*synthetic*/ final JTextComponent$AccessibleJTextComponent this$1;
    /*synthetic*/ final JTextComponent val$this$0;
    
    JTextComponent$AccessibleJTextComponent$1(/*synthetic*/ final JTextComponent$AccessibleJTextComponent this$1, /*synthetic*/ final JTextComponent val$this$0) {
        this.this$1 = this$1;
        this.val$this$0 = val$this$0;
        
    }
    
    public void componentMoved(ComponentEvent e) {
        try {
            Point newLocationOnScreen = this$1.getLocationOnScreen();
            this$1.firePropertyChange("AccessibleVisibleData", this$1.oldLocationOnScreen, newLocationOnScreen);
            this$1.oldLocationOnScreen = newLocationOnScreen;
        } catch (IllegalComponentStateException iae) {
        }
    }
}
