package javax.swing;

import java.awt.event.*;
import java.beans.*;
import java.util.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.plaf.basic.*;
import javax.accessibility.*;

class JMenu$1 extends JMenuItem {
    /*synthetic*/ final JMenu this$0;
    
    JMenu$1(/*synthetic*/ final JMenu this$0, .java.lang.String x0, .javax.swing.Icon x1) {
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
