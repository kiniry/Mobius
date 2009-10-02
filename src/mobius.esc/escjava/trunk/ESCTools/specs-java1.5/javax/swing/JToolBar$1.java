package javax.swing;

import java.awt.event.*;
import java.beans.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

class JToolBar$1 extends JButton {
    /*synthetic*/ final JToolBar this$0;
    
    JToolBar$1(/*synthetic*/ final JToolBar this$0, .java.lang.String x0, .javax.swing.Icon x1) {
        this.this$0 = this$0;
        super(x0, x1);
    }
    
    protected PropertyChangeListener createActionPropertyChangeListener(Action a) {
        PropertyChangeListener pcl = this$0.createActionChangeListener(this);
        if (pcl == null) {
            pcl = super.createActionPropertyChangeListener(a);
        }
        return pcl;
    }
}
