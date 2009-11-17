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

class JTable$3 implements JTable$Resizable3 {
    /*synthetic*/ final JTable this$0;
    /*synthetic*/ final TableColumnModel val$cm;
    /*synthetic*/ final int val$start;
    /*synthetic*/ final int val$end;
    
    JTable$3(/*synthetic*/ final JTable this$0, /*synthetic*/ final int val$end, /*synthetic*/ final int val$start, /*synthetic*/ final TableColumnModel val$cm) {
        this.this$0 = this$0;
        this.val$end = val$end;
        this.val$start = val$start;
        this.val$cm = val$cm;
        
    }
    
    public int getElementCount() {
        return val$end - val$start;
    }
    
    public int getLowerBoundAt(int i) {
        return val$cm.getColumn(i + val$start).getMinWidth();
    }
    
    public int getUpperBoundAt(int i) {
        return val$cm.getColumn(i + val$start).getMaxWidth();
    }
    
    public int getMidPointAt(int i) {
        return val$cm.getColumn(i + val$start).getWidth();
    }
    
    public void setSizeAt(int s, int i) {
        val$cm.getColumn(i + val$start).setWidth(s);
    }
}
