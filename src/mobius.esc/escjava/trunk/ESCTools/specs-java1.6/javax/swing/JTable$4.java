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

class JTable$4 implements JTable$Resizable2 {
    /*synthetic*/ final JTable this$0;
    /*synthetic*/ final JTable$Resizable3 val$r;
    
    JTable$4(/*synthetic*/ final JTable this$0, /*synthetic*/ final JTable$Resizable3 val$r) {
        this.this$0 = this$0;
        this.val$r = val$r;
        
    }
    
    public int getElementCount() {
        return val$r.getElementCount();
    }
    
    public int getLowerBoundAt(int i) {
        return val$r.getLowerBoundAt(i);
    }
    
    public int getUpperBoundAt(int i) {
        return val$r.getMidPointAt(i);
    }
    
    public void setSizeAt(int newSize, int i) {
        val$r.setSizeAt(newSize, i);
    }
}
