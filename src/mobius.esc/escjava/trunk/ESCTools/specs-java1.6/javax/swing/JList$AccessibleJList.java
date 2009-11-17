package javax.swing;

import java.awt.event.*;
import java.awt.*;
import java.beans.*;
import javax.swing.event.*;
import javax.accessibility.*;
import javax.swing.plaf.*;

public class JList$AccessibleJList extends JComponent$AccessibleJComponent implements AccessibleSelection, PropertyChangeListener, ListSelectionListener, ListDataListener {
    /*synthetic*/ final JList this$0;
    int leadSelectionIndex;
    
    public JList$AccessibleJList(/*synthetic*/ final JList this$0) {
        super(this$0);
        this.this$0 = this$0;
        this$0.addPropertyChangeListener(this);
        this$0.getSelectionModel().addListSelectionListener(this);
        this$0.getModel().addListDataListener(this);
        leadSelectionIndex = this$0.getLeadSelectionIndex();
    }
    
    public void propertyChange(PropertyChangeEvent e) {
        String name = e.getPropertyName();
        Object oldValue = e.getOldValue();
        Object newValue = e.getNewValue();
        if (name.compareTo("model") == 0) {
            if (oldValue != null && oldValue instanceof ListModel) {
                ((ListModel)(ListModel)oldValue).removeListDataListener(this);
            }
            if (newValue != null && newValue instanceof ListModel) {
                ((ListModel)(ListModel)newValue).addListDataListener(this);
            }
        } else if (name.compareTo("selectionModel") == 0) {
            if (oldValue != null && oldValue instanceof ListSelectionModel) {
                ((ListSelectionModel)(ListSelectionModel)oldValue).removeListSelectionListener(this);
            }
            if (newValue != null && newValue instanceof ListSelectionModel) {
                ((ListSelectionModel)(ListSelectionModel)newValue).addListSelectionListener(this);
            }
            firePropertyChange(AccessibleContext.ACCESSIBLE_SELECTION_PROPERTY, Boolean.valueOf(false), Boolean.valueOf(true));
        }
    }
    
    public void valueChanged(ListSelectionEvent e) {
        int oldLeadSelectionIndex = leadSelectionIndex;
        leadSelectionIndex = this$0.getLeadSelectionIndex();
        if (oldLeadSelectionIndex != leadSelectionIndex) {
            Accessible oldLS;
            Accessible newLS;
            oldLS = (oldLeadSelectionIndex >= 0) ? getAccessibleChild(oldLeadSelectionIndex) : null;
            newLS = (leadSelectionIndex >= 0) ? getAccessibleChild(leadSelectionIndex) : null;
            firePropertyChange(AccessibleContext.ACCESSIBLE_ACTIVE_DESCENDANT_PROPERTY, oldLS, newLS);
        }
        firePropertyChange(AccessibleContext.ACCESSIBLE_VISIBLE_DATA_PROPERTY, Boolean.valueOf(false), Boolean.valueOf(true));
        firePropertyChange(AccessibleContext.ACCESSIBLE_SELECTION_PROPERTY, Boolean.valueOf(false), Boolean.valueOf(true));
        AccessibleStateSet s = getAccessibleStateSet();
        ListSelectionModel lsm = this$0.getSelectionModel();
        if (lsm.getSelectionMode() != ListSelectionModel.SINGLE_SELECTION) {
            if (!s.contains(AccessibleState.MULTISELECTABLE)) {
                s.add(AccessibleState.MULTISELECTABLE);
                firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, null, AccessibleState.MULTISELECTABLE);
            }
        } else {
            if (s.contains(AccessibleState.MULTISELECTABLE)) {
                s.remove(AccessibleState.MULTISELECTABLE);
                firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, AccessibleState.MULTISELECTABLE, null);
            }
        }
    }
    
    public void intervalAdded(ListDataEvent e) {
        firePropertyChange(AccessibleContext.ACCESSIBLE_VISIBLE_DATA_PROPERTY, Boolean.valueOf(false), Boolean.valueOf(true));
    }
    
    public void intervalRemoved(ListDataEvent e) {
        firePropertyChange(AccessibleContext.ACCESSIBLE_VISIBLE_DATA_PROPERTY, Boolean.valueOf(false), Boolean.valueOf(true));
    }
    
    public void contentsChanged(ListDataEvent e) {
        firePropertyChange(AccessibleContext.ACCESSIBLE_VISIBLE_DATA_PROPERTY, Boolean.valueOf(false), Boolean.valueOf(true));
    }
    
    public AccessibleStateSet getAccessibleStateSet() {
        AccessibleStateSet states = super.getAccessibleStateSet();
        if (JList.access$100(this$0).getSelectionMode() != ListSelectionModel.SINGLE_SELECTION) {
            states.add(AccessibleState.MULTISELECTABLE);
        }
        return states;
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.LIST;
    }
    
    public Accessible getAccessibleAt(Point p) {
        int i = this$0.locationToIndex(p);
        if (i >= 0) {
            return new JList$AccessibleJList$AccessibleJListChild(this, this$0, i);
        } else {
            return null;
        }
    }
    
    public int getAccessibleChildrenCount() {
        return this$0.getModel().getSize();
    }
    
    public Accessible getAccessibleChild(int i) {
        if (i >= this$0.getModel().getSize()) {
            return null;
        } else {
            return new JList$AccessibleJList$AccessibleJListChild(this, this$0, i);
        }
    }
    
    public AccessibleSelection getAccessibleSelection() {
        return this;
    }
    
    public int getAccessibleSelectionCount() {
        return this$0.getSelectedIndices().length;
    }
    
    public Accessible getAccessibleSelection(int i) {
        int len = getAccessibleSelectionCount();
        if (i < 0 || i >= len) {
            return null;
        } else {
            return getAccessibleChild(this$0.getSelectedIndices()[i]);
        }
    }
    
    public boolean isAccessibleChildSelected(int i) {
        return this$0.isSelectedIndex(i);
    }
    
    public void addAccessibleSelection(int i) {
        this$0.addSelectionInterval(i, i);
    }
    
    public void removeAccessibleSelection(int i) {
        this$0.removeSelectionInterval(i, i);
    }
    
    public void clearAccessibleSelection() {
        this$0.clearSelection();
    }
    
    public void selectAllAccessibleSelection() {
        this$0.addSelectionInterval(0, getAccessibleChildrenCount() - 1);
    }
    {
    }
}
