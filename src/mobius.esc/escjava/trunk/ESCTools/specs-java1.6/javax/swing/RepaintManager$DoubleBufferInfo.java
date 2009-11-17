package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.util.*;
import java.applet.*;

class RepaintManager$DoubleBufferInfo {
    
    /*synthetic*/ RepaintManager$DoubleBufferInfo(RepaintManager x0, javax.swing.RepaintManager$1 x1) {
        this(x0);
    }
    /*synthetic*/ final RepaintManager this$0;
    
    private RepaintManager$DoubleBufferInfo(/*synthetic*/ final RepaintManager this$0) {
        this.this$0 = this$0;
        
    }
    public Image image;
    public Dimension size;
    public boolean needsReset = false;
}
