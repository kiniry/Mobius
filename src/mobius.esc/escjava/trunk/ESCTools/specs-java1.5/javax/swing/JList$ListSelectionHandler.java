package javax.swing;

import java.awt.event.*;
import java.awt.*;
import java.beans.*;
import javax.swing.event.*;
import javax.accessibility.*;
import javax.swing.plaf.*;
import java.io.Serializable;

class JList$ListSelectionHandler implements ListSelectionListener, Serializable {
    
    /*synthetic*/ JList$ListSelectionHandler(JList x0, javax.swing.JList$1 x1) {
        this(x0);
    }
    /*synthetic*/ final JList this$0;
    
    private JList$ListSelectionHandler(/*synthetic*/ final JList this$0) {
        this.this$0 = this$0;
        
    }
    
    public void valueChanged(ListSelectionEvent e) {
        this$0.fireSelectionValueChanged(e.getFirstIndex(), e.getLastIndex(), e.getValueIsAdjusting());
    }
}
