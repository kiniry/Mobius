package javax.swing.text;

import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.beans.*;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;

class DefaultCaret$1 implements Runnable {
    /*synthetic*/ final DefaultCaret this$0;
    
    DefaultCaret$1(/*synthetic*/ final DefaultCaret this$0) {
        this.this$0 = this$0;
        
    }
    
    public void run() {
        this$0.repaintNewCaret();
    }
}
