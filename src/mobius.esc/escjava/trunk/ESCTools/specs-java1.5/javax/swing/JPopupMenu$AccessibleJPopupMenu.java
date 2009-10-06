package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.accessibility.*;
import javax.swing.plaf.basic.BasicComboPopup;
import javax.swing.event.*;

public class JPopupMenu$AccessibleJPopupMenu extends JComponent$AccessibleJComponent implements PropertyChangeListener {
    /*synthetic*/ final JPopupMenu this$0;
    
    protected JPopupMenu$AccessibleJPopupMenu(/*synthetic*/ final JPopupMenu this$0) {
        super(this$0);
        this.this$0 = this$0;
        this$0.addPropertyChangeListener(this);
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.POPUP_MENU;
    }
    
    public void propertyChange(PropertyChangeEvent e) {
        String propertyName = e.getPropertyName();
        if (propertyName == "visible") {
            if (e.getOldValue() == Boolean.FALSE && e.getNewValue() == Boolean.TRUE) {
                handlePopupIsVisibleEvent(true);
            } else if (e.getOldValue() == Boolean.TRUE && e.getNewValue() == Boolean.FALSE) {
                handlePopupIsVisibleEvent(false);
            }
        }
    }
    
    private void handlePopupIsVisibleEvent(boolean visible) {
        if (visible) {
            firePropertyChange(ACCESSIBLE_STATE_PROPERTY, null, AccessibleState.VISIBLE);
            fireActiveDescendant();
        } else {
            firePropertyChange(ACCESSIBLE_STATE_PROPERTY, AccessibleState.VISIBLE, null);
        }
    }
    
    private void fireActiveDescendant() {
        if (this$0 instanceof BasicComboPopup) {
            JList popupList = ((BasicComboPopup)(BasicComboPopup)this$0).getList();
            if (popupList == null) {
                return;
            }
            AccessibleContext ac = popupList.getAccessibleContext();
            AccessibleSelection selection = ac.getAccessibleSelection();
            if (selection == null) {
                return;
            }
            Accessible a = selection.getAccessibleSelection(0);
            if (a == null) {
                return;
            }
            AccessibleContext selectedItem = a.getAccessibleContext();
            if (selectedItem != null && this$0.invoker != null) {
                AccessibleContext invokerContext = this$0.invoker.getAccessibleContext();
                if (invokerContext != null) {
                    invokerContext.firePropertyChange(ACCESSIBLE_ACTIVE_DESCENDANT_PROPERTY, null, selectedItem);
                }
            }
        }
    }
}
