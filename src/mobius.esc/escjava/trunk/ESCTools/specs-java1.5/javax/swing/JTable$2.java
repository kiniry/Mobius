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

class JTable$2 implements JTable$Resizable3 {
    /*synthetic*/ final JTable this$0;
    /*synthetic*/ final boolean val$inverse;
    /*synthetic*/ final TableColumnModel val$cm;
    
    JTable$2(/*synthetic*/ final JTable this$0, /*synthetic*/ final TableColumnModel val$cm, /*synthetic*/ final boolean val$inverse) {
        this.this$0 = this$0;
        this.val$cm = val$cm;
        this.val$inverse = val$inverse;
        
    }
    
    public int getElementCount() {
        return val$cm.getColumnCount();
    }
    
    public int getLowerBoundAt(int i) {
        return val$cm.getColumn(i).getMinWidth();
    }
    
    public int getUpperBoundAt(int i) {
        return val$cm.getColumn(i).getMaxWidth();
    }
    
    public int getMidPointAt(int i) {
        if (!val$inverse) {
            return val$cm.getColumn(i).getPreferredWidth();
        } else {
            return val$cm.getColumn(i).getWidth();
        }
    }
    
    public void setSizeAt(int s, int i) {
        if (!val$inverse) {
            val$cm.getColumn(i).setWidth(s);
        } else {
            val$cm.getColumn(i).setPreferredWidth(s);
        }
    }
}
