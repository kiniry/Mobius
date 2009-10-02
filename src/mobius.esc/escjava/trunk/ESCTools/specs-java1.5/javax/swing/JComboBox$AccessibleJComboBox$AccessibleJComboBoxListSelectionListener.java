package javax.swing;

import java.beans.*;
import java.util.*;
import java.awt.*;
import java.awt.event.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.border.*;
import javax.accessibility.*;

class JComboBox$AccessibleJComboBox$AccessibleJComboBoxListSelectionListener implements ListSelectionListener {
    
    /*synthetic*/ JComboBox$AccessibleJComboBox$AccessibleJComboBoxListSelectionListener(JComboBox.AccessibleJComboBox x0, javax.swing.JComboBox$1 x1) {
        this(x0);
    }
    /*synthetic*/ final JComboBox$AccessibleJComboBox this$1;
    
    private JComboBox$AccessibleJComboBox$AccessibleJComboBoxListSelectionListener(/*synthetic*/ final JComboBox$AccessibleJComboBox this$1) {
        this.this$1 = this$1;
        
    }
    
    public void valueChanged(ListSelectionEvent e) {
        if (JComboBox.AccessibleJComboBox.access$200(this$1) == null) {
            return;
        }
        int selectedIndex = JComboBox.AccessibleJComboBox.access$200(this$1).getSelectedIndex();
        if (selectedIndex < 0) {
            return;
        }
        Accessible selectedAccessible = JComboBox.AccessibleJComboBox.access$200(this$1).getAccessibleContext().getAccessibleChild(selectedIndex);
        if (selectedAccessible == null) {
            return;
        }
        PropertyChangeEvent pce = null;
        if (JComboBox.AccessibleJComboBox.access$300(this$1) != null) {
            pce = new PropertyChangeEvent(JComboBox.AccessibleJComboBox.access$300(this$1), AccessibleContext.ACCESSIBLE_STATE_PROPERTY, AccessibleState.FOCUSED, null);
            this$1.firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, null, pce);
        }
        pce = new PropertyChangeEvent(selectedAccessible, AccessibleContext.ACCESSIBLE_STATE_PROPERTY, null, AccessibleState.FOCUSED);
        this$1.firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, null, pce);
        this$1.firePropertyChange(AccessibleContext.ACCESSIBLE_ACTIVE_DESCENDANT_PROPERTY, JComboBox.AccessibleJComboBox.access$300(this$1), selectedAccessible);
        JComboBox.AccessibleJComboBox.access$302(this$1, selectedAccessible);
    }
}
