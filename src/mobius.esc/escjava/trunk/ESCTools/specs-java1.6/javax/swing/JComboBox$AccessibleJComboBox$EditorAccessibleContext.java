package javax.swing;

import java.beans.*;
import java.util.*;
import java.awt.*;
import java.awt.event.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.border.*;
import javax.accessibility.*;

class JComboBox$AccessibleJComboBox$EditorAccessibleContext extends AccessibleContext {
    /*synthetic*/ final JComboBox$AccessibleJComboBox this$1;
    private AccessibleContext ac;
    
    private JComboBox$AccessibleJComboBox$EditorAccessibleContext(/*synthetic*/ final JComboBox$AccessibleJComboBox this$1) {
        this.this$1 = this$1;
        
    }
    
    JComboBox$AccessibleJComboBox$EditorAccessibleContext(/*synthetic*/ final JComboBox$AccessibleJComboBox this$1, Accessible a) {
        this.this$1 = this$1;
        
        this.ac = a.getAccessibleContext();
    }
    
    public String getAccessibleName() {
        return ac.getAccessibleName();
    }
    
    public void setAccessibleName(String s) {
        ac.setAccessibleName(s);
    }
    
    public String getAccessibleDescription() {
        return ac.getAccessibleDescription();
    }
    
    public void setAccessibleDescription(String s) {
        ac.setAccessibleDescription(s);
    }
    
    public AccessibleRole getAccessibleRole() {
        return ac.getAccessibleRole();
    }
    
    public AccessibleStateSet getAccessibleStateSet() {
        return ac.getAccessibleStateSet();
    }
    
    public Accessible getAccessibleParent() {
        return ac.getAccessibleParent();
    }
    
    public void setAccessibleParent(Accessible a) {
        ac.setAccessibleParent(a);
    }
    
    public int getAccessibleIndexInParent() {
        return this$1.this$0.getSelectedIndex();
    }
    
    public int getAccessibleChildrenCount() {
        return ac.getAccessibleChildrenCount();
    }
    
    public Accessible getAccessibleChild(int i) {
        return ac.getAccessibleChild(i);
    }
    
    public Locale getLocale() throws IllegalComponentStateException {
        return ac.getLocale();
    }
    
    public void addPropertyChangeListener(PropertyChangeListener listener) {
        ac.addPropertyChangeListener(listener);
    }
    
    public void removePropertyChangeListener(PropertyChangeListener listener) {
        ac.removePropertyChangeListener(listener);
    }
    
    public AccessibleAction getAccessibleAction() {
        return ac.getAccessibleAction();
    }
    
    public AccessibleComponent getAccessibleComponent() {
        return ac.getAccessibleComponent();
    }
    
    public AccessibleSelection getAccessibleSelection() {
        return ac.getAccessibleSelection();
    }
    
    public AccessibleText getAccessibleText() {
        return ac.getAccessibleText();
    }
    
    public AccessibleEditableText getAccessibleEditableText() {
        return ac.getAccessibleEditableText();
    }
    
    public AccessibleValue getAccessibleValue() {
        return ac.getAccessibleValue();
    }
    
    public AccessibleIcon[] getAccessibleIcon() {
        return ac.getAccessibleIcon();
    }
    
    public AccessibleRelationSet getAccessibleRelationSet() {
        return ac.getAccessibleRelationSet();
    }
    
    public AccessibleTable getAccessibleTable() {
        return ac.getAccessibleTable();
    }
    
    public void firePropertyChange(String propertyName, Object oldValue, Object newValue) {
        ac.firePropertyChange(propertyName, oldValue, newValue);
    }
}
