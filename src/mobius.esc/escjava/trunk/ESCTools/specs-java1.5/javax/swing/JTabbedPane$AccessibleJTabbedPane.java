package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.util.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

public class JTabbedPane$AccessibleJTabbedPane extends JComponent$AccessibleJComponent implements AccessibleSelection, ChangeListener {
    /*synthetic*/ final JTabbedPane this$0;
    
    public JTabbedPane$AccessibleJTabbedPane(/*synthetic*/ final JTabbedPane this$0) {
        super(this$0);
        this.this$0 = this$0;
        this$0.model.addChangeListener(this);
    }
    
    public void stateChanged(ChangeEvent e) {
        Object o = e.getSource();
        firePropertyChange(AccessibleContext.ACCESSIBLE_SELECTION_PROPERTY, null, o);
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.PAGE_TAB_LIST;
    }
    
    public int getAccessibleChildrenCount() {
        return this$0.getTabCount();
    }
    
    public Accessible getAccessibleChild(int i) {
        if (i < 0 || i >= this$0.getTabCount()) {
            return null;
        }
        return (Accessible)(Accessible)this$0.pages.elementAt(i);
    }
    
    public AccessibleSelection getAccessibleSelection() {
        return this;
    }
    
    public Accessible getAccessibleAt(Point p) {
        int tab = ((TabbedPaneUI)(TabbedPaneUI)this$0.ui).tabForCoordinate(this$0, p.x, p.y);
        if (tab == -1) {
            tab = this$0.getSelectedIndex();
        }
        return getAccessibleChild(tab);
    }
    
    public int getAccessibleSelectionCount() {
        return 1;
    }
    
    public Accessible getAccessibleSelection(int i) {
        int index = this$0.getSelectedIndex();
        if (index == -1) {
            return null;
        }
        return (Accessible)(Accessible)this$0.pages.elementAt(index);
    }
    
    public boolean isAccessibleChildSelected(int i) {
        return (i == this$0.getSelectedIndex());
    }
    
    public void addAccessibleSelection(int i) {
        this$0.setSelectedIndex(i);
    }
    
    public void removeAccessibleSelection(int i) {
    }
    
    public void clearAccessibleSelection() {
    }
    
    public void selectAllAccessibleSelection() {
    }
}
