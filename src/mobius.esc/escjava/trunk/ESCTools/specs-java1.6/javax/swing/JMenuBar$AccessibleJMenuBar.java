package javax.swing;

import java.awt.event.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

public class JMenuBar$AccessibleJMenuBar extends JComponent$AccessibleJComponent implements AccessibleSelection {
    /*synthetic*/ final JMenuBar this$0;
    
    protected JMenuBar$AccessibleJMenuBar(/*synthetic*/ final JMenuBar this$0) {
        super(this$0);
        this.this$0 = this$0;
    }
    
    public AccessibleStateSet getAccessibleStateSet() {
        AccessibleStateSet states = super.getAccessibleStateSet();
        return states;
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.MENU_BAR;
    }
    
    public AccessibleSelection getAccessibleSelection() {
        return this;
    }
    
    public int getAccessibleSelectionCount() {
        if (this$0.isSelected()) {
            return 1;
        } else {
            return 0;
        }
    }
    
    public Accessible getAccessibleSelection(int i) {
        if (this$0.isSelected()) {
            if (i != 0) {
                return null;
            }
            int j = this$0.getSelectionModel().getSelectedIndex();
            if (this$0.getComponentAtIndex(j) instanceof Accessible) {
                return (Accessible)(Accessible)this$0.getComponentAtIndex(j);
            }
        }
        return null;
    }
    
    public boolean isAccessibleChildSelected(int i) {
        return (i == this$0.getSelectionModel().getSelectedIndex());
    }
    
    public void addAccessibleSelection(int i) {
        int j = this$0.getSelectionModel().getSelectedIndex();
        if (i == j) {
            return;
        }
        if (j >= 0 && j < this$0.getMenuCount()) {
            JMenu menu = this$0.getMenu(j);
            if (menu != null) {
                MenuSelectionManager.defaultManager().setSelectedPath(null);
            }
        }
        this$0.getSelectionModel().setSelectedIndex(i);
        JMenu menu = this$0.getMenu(i);
        if (menu != null) {
            MenuElement[] me = new MenuElement[3];
            me[0] = this$0;
            me[1] = menu;
            me[2] = menu.getPopupMenu();
            MenuSelectionManager.defaultManager().setSelectedPath(me);
        }
    }
    
    public void removeAccessibleSelection(int i) {
        if (i >= 0 && i < this$0.getMenuCount()) {
            JMenu menu = this$0.getMenu(i);
            if (menu != null) {
                MenuSelectionManager.defaultManager().setSelectedPath(null);
            }
            this$0.getSelectionModel().setSelectedIndex(-1);
        }
    }
    
    public void clearAccessibleSelection() {
        int i = this$0.getSelectionModel().getSelectedIndex();
        if (i >= 0 && i < this$0.getMenuCount()) {
            JMenu menu = this$0.getMenu(i);
            if (menu != null) {
                MenuSelectionManager.defaultManager().setSelectedPath(null);
            }
        }
        this$0.getSelectionModel().setSelectedIndex(-1);
    }
    
    public void selectAllAccessibleSelection() {
    }
}
