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

class JTextComponent$AccessibleJTextComponent$4 implements Runnable {
    /*synthetic*/ final JTextComponent$AccessibleJTextComponent this$1;
    /*synthetic*/ final Integer val$pos;
    
    JTextComponent$AccessibleJTextComponent$4(/*synthetic*/ final JTextComponent$AccessibleJTextComponent this$1, /*synthetic*/ final Integer val$pos) {
        this.this$1 = this$1;
        this.val$pos = val$pos;
        
    }
    
    public void run() {
        this$1.firePropertyChange("AccessibleText", null, val$pos);
    }
}
