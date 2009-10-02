package javax.swing;

import java.util.*;
import java.applet.Applet;
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

class JTable$CellEditorRemover implements PropertyChangeListener {
    /*synthetic*/ final JTable this$0;
    KeyboardFocusManager focusManager;
    
    public JTable$CellEditorRemover(/*synthetic*/ final JTable this$0, KeyboardFocusManager fm) {
        this.this$0 = this$0;
        
        this.focusManager = fm;
    }
    
    public void propertyChange(PropertyChangeEvent ev) {
        if (!this$0.isEditing() || this$0.getClientProperty("terminateEditOnFocusLost") != Boolean.TRUE) {
            return;
        }
        Component c = focusManager.getPermanentFocusOwner();
        while (c != null) {
            if (c == this$0) {
                return;
            } else if ((c instanceof Window) || (c instanceof Applet && c.getParent() == null)) {
                if (c == SwingUtilities.getRoot(this$0)) {
                    if (!this$0.getCellEditor().stopCellEditing()) {
                        this$0.getCellEditor().cancelCellEditing();
                    }
                }
                break;
            }
            c = c.getParent();
        }
    }
}
