package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.border.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

public class JComponent$AccessibleJComponent$AccessibleContainerHandler implements ContainerListener {
    /*synthetic*/ final JComponent$AccessibleJComponent this$1;
    
    protected JComponent$AccessibleJComponent$AccessibleContainerHandler(/*synthetic*/ final JComponent$AccessibleJComponent this$1) {
        this.this$1 = this$1;
        
    }
    
    public void componentAdded(ContainerEvent e) {
        Component c = e.getChild();
        if (c != null && c instanceof Accessible) {
            this$1.firePropertyChange(AccessibleContext.ACCESSIBLE_CHILD_PROPERTY, null, ((Accessible)(Accessible)c).getAccessibleContext());
        }
    }
    
    public void componentRemoved(ContainerEvent e) {
        Component c = e.getChild();
        if (c != null && c instanceof Accessible) {
            this$1.firePropertyChange(AccessibleContext.ACCESSIBLE_CHILD_PROPERTY, ((Accessible)(Accessible)c).getAccessibleContext(), null);
        }
    }
}
