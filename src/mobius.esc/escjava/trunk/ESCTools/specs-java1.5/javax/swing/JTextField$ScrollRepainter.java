package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.text.*;
import javax.swing.plaf.*;
import javax.swing.event.*;
import javax.accessibility.*;
import java.io.Serializable;

class JTextField$ScrollRepainter implements ChangeListener, Serializable {
    /*synthetic*/ final JTextField this$0;
    
    JTextField$ScrollRepainter(/*synthetic*/ final JTextField this$0) {
        this.this$0 = this$0;
        
    }
    
    public void stateChanged(ChangeEvent e) {
        this$0.repaint();
    }
}
