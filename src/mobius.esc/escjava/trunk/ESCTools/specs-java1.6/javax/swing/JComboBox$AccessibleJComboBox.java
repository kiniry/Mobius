package javax.swing;

import java.beans.*;
import java.util.*;
import java.awt.*;
import java.awt.event.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.border.*;
import javax.accessibility.*;

public class JComboBox$AccessibleJComboBox extends JComponent$AccessibleJComponent implements AccessibleAction, AccessibleSelection {
    
    /*synthetic*/ static JComboBox$AccessibleJComboBox$EditorAccessibleContext access$402(JComboBox$AccessibleJComboBox x0, JComboBox$AccessibleJComboBox$EditorAccessibleContext x1) {
        return x0.editorAccessibleContext = x1;
    }
    
    /*synthetic*/ static JComboBox$AccessibleJComboBox$EditorAccessibleContext access$400(JComboBox$AccessibleJComboBox x0) {
        return x0.editorAccessibleContext;
    }
    
    /*synthetic*/ static Accessible access$302(JComboBox$AccessibleJComboBox x0, Accessible x1) {
        return x0.previousSelectedAccessible = x1;
    }
    
    /*synthetic*/ static Accessible access$300(JComboBox$AccessibleJComboBox x0) {
        return x0.previousSelectedAccessible;
    }
    
    /*synthetic*/ static JList access$200(JComboBox$AccessibleJComboBox x0) {
        return x0.popupList;
    }
    /*synthetic*/ final JComboBox this$0;
    private JList popupList;
    private Accessible previousSelectedAccessible = null;
    
    public JComboBox$AccessibleJComboBox(/*synthetic*/ final JComboBox this$0) {
        super(this$0);
        this.this$0 = this$0;
        Accessible a = this$0.getUI().getAccessibleChild(this$0, 0);
        if (a instanceof javax.swing.plaf.basic.ComboPopup) {
            popupList = ((javax.swing.plaf.basic.ComboPopup)(javax.swing.plaf.basic.ComboPopup)a).getList();
            popupList.addListSelectionListener(new JComboBox$AccessibleJComboBox$AccessibleJComboBoxListSelectionListener(this, null));
        }
        this$0.addPopupMenuListener(new JComboBox$AccessibleJComboBox$AccessibleJComboBoxPopupMenuListener(this, null));
    }
    {
    }
    {
    }
    
    public int getAccessibleChildrenCount() {
        if (this$0.ui != null) {
            return this$0.ui.getAccessibleChildrenCount(this$0);
        } else {
            return super.getAccessibleChildrenCount();
        }
    }
    
    public Accessible getAccessibleChild(int i) {
        if (this$0.ui != null) {
            return this$0.ui.getAccessibleChild(this$0, i);
        } else {
            return super.getAccessibleChild(i);
        }
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.COMBO_BOX;
    }
    
    public AccessibleStateSet getAccessibleStateSet() {
        AccessibleStateSet ass = super.getAccessibleStateSet();
        if (ass == null) {
            ass = new AccessibleStateSet();
        }
        if (this$0.isPopupVisible()) {
            ass.add(AccessibleState.EXPANDED);
        } else {
            ass.add(AccessibleState.COLLAPSED);
        }
        return ass;
    }
    
    public AccessibleAction getAccessibleAction() {
        return this;
    }
    
    public String getAccessibleActionDescription(int i) {
        if (i == 0) {
            return UIManager.getString("ComboBox.togglePopupText");
        } else {
            return null;
        }
    }
    
    public int getAccessibleActionCount() {
        return 1;
    }
    
    public boolean doAccessibleAction(int i) {
        if (i == 0) {
            this$0.setPopupVisible(!this$0.isPopupVisible());
            return true;
        } else {
            return false;
        }
    }
    
    public AccessibleSelection getAccessibleSelection() {
        return this;
    }
    
    public int getAccessibleSelectionCount() {
        Object o = this$0.getSelectedItem();
        if (o != null) {
            return 1;
        } else {
            return 0;
        }
    }
    
    public Accessible getAccessibleSelection(int i) {
        Accessible a = this$0.getUI().getAccessibleChild(this$0, 0);
        if (a != null && a instanceof javax.swing.plaf.basic.ComboPopup) {
            JList list = ((javax.swing.plaf.basic.ComboPopup)(javax.swing.plaf.basic.ComboPopup)a).getList();
            AccessibleContext ac = list.getAccessibleContext();
            if (ac != null) {
                AccessibleSelection as = ac.getAccessibleSelection();
                if (as != null) {
                    return as.getAccessibleSelection(i);
                }
            }
        }
        return null;
    }
    
    public boolean isAccessibleChildSelected(int i) {
        return this$0.getSelectedIndex() == i;
    }
    
    public void addAccessibleSelection(int i) {
        clearAccessibleSelection();
        this$0.setSelectedIndex(i);
    }
    
    public void removeAccessibleSelection(int i) {
        if (this$0.getSelectedIndex() == i) {
            clearAccessibleSelection();
        }
    }
    
    public void clearAccessibleSelection() {
        this$0.setSelectedIndex(-1);
    }
    
    public void selectAllAccessibleSelection() {
    }
    private JComboBox$AccessibleJComboBox$EditorAccessibleContext editorAccessibleContext = null;
    {
    }
    {
    }
}
