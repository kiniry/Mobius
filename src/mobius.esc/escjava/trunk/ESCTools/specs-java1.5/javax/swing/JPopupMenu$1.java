package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.accessibility.*;
import javax.swing.event.*;

class JPopupMenu$1 extends JMenuItem {
    /*synthetic*/ final JPopupMenu this$0;
    
    JPopupMenu$1(/*synthetic*/ final JPopupMenu this$0, java.lang.String x0, javax.swing.Icon x1) {
        super(x0, x1);
        this.this$0 = this$0;
    }
    
    protected PropertyChangeListener createActionPropertyChangeListener(Action a) {
        PropertyChangeListener pcl = this$0.createActionChangeListener(this);
        if (pcl == null) {
            pcl = super.createActionPropertyChangeListener(a);
        }
        return pcl;
    }
}
