package javax.swing.text;

import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.beans.*;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;

class DefaultCaret$SafeScroller implements Runnable {
    /*synthetic*/ final DefaultCaret this$0;
    
    DefaultCaret$SafeScroller(/*synthetic*/ final DefaultCaret this$0, Rectangle r) {
        this.this$0 = this$0;
        
        this.r = r;
    }
    
    public void run() {
        if (this$0.component != null) {
            this$0.component.scrollRectToVisible(r);
        }
    }
    Rectangle r;
}
