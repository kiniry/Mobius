package javax.swing;

import java.awt.Component;
import java.awt.event.*;
import java.beans.*;
import java.util.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.plaf.basic.*;
import javax.accessibility.*;

public class JMenu$AccessibleJMenu extends JMenuItem$AccessibleJMenuItem implements AccessibleSelection {
    /*synthetic*/ final JMenu this$0;
    
    protected JMenu$AccessibleJMenu(/*synthetic*/ final JMenu this$0) {
        this.this$0 = this$0;
        super(this$0);
    }
    
    public int getAccessibleChildrenCount() {
        Component[] children = this$0.getMenuComponents();
        int count = 0;
        for (int j = 0; j < children.length; j++) {
            if (children[j] instanceof Accessible) {
                count++;
            }
        }
        return count;
    }
    
    public Accessible getAccessibleChild(int i) {
        Component[] children = this$0.getMenuComponents();
        int count = 0;
        for (int j = 0; j < children.length; j++) {
            if (children[j] instanceof Accessible) {
                if (count == i) {
                    if (children[j] instanceof JComponent) {
                        AccessibleContext ac = ((Accessible)(Accessible)children[j]).getAccessibleContext();
                        ac.setAccessibleParent(this$0);
                    }
                    return (Accessible)(Accessible)children[j];
                } else {
                    count++;
                }
            }
        }
        return null;
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.MENU;
    }
    
    public AccessibleSelection getAccessibleSelection() {
        return this;
    }
    
    public int getAccessibleSelectionCount() {
        MenuElement[] me = MenuSelectionManager.defaultManager().getSelectedPath();
        if (me != null) {
            for (int i = 0; i < me.length; i++) {
                if (me[i] == this$0) {
                    if (i + 1 < me.length) {
                        return 1;
                    }
                }
            }
        }
        return 0;
    }
    
    public Accessible getAccessibleSelection(int i) {
        if (i < 0 || i >= this$0.getItemCount()) {
            return null;
        }
        MenuElement[] me = MenuSelectionManager.defaultManager().getSelectedPath();
        if (me != null) {
            for (int j = 0; j < me.length; j++) {
                if (me[j] == this$0) {
                    while (++j < me.length) {
                        if (me[j] instanceof JMenuItem) {
                            return (Accessible)(Accessible)me[j];
                        }
                    }
                }
            }
        }
        return null;
    }
    
    public boolean isAccessibleChildSelected(int i) {
        MenuElement[] me = MenuSelectionManager.defaultManager().getSelectedPath();
        if (me != null) {
            JMenuItem mi = this$0.getItem(i);
            for (int j = 0; j < me.length; j++) {
                if (me[j] == mi) {
                    return true;
                }
            }
        }
        return false;
    }
    
    public void addAccessibleSelection(int i) {
        if (i < 0 || i >= this$0.getItemCount()) {
            return;
        }
        JMenuItem mi = this$0.getItem(i);
        if (mi != null) {
            if (mi instanceof JMenu) {
                MenuElement[] me = JMenu.access$000(this$0, (JMenu)(JMenu)mi);
                MenuSelectionManager.defaultManager().setSelectedPath(me);
            } else {
                mi.doClick();
                MenuSelectionManager.defaultManager().setSelectedPath(null);
            }
        }
    }
    
    public void removeAccessibleSelection(int i) {
        if (i < 0 || i >= this$0.getItemCount()) {
            return;
        }
        JMenuItem mi = this$0.getItem(i);
        if (mi != null && mi instanceof JMenu) {
            if (((JMenu)(JMenu)mi).isSelected()) {
                MenuElement[] old = MenuSelectionManager.defaultManager().getSelectedPath();
                MenuElement[] me = new MenuElement[old.length - 2];
                for (int j = 0; j < old.length - 2; j++) {
                    me[j] = old[j];
                }
                MenuSelectionManager.defaultManager().setSelectedPath(me);
            }
        }
    }
    
    public void clearAccessibleSelection() {
        MenuElement[] old = MenuSelectionManager.defaultManager().getSelectedPath();
        if (old != null) {
            for (int j = 0; j < old.length; j++) {
                if (old[j] == this$0) {
                    MenuElement[] me = new MenuElement[j + 1];
                    System.arraycopy(old, 0, me, 0, j);
                    me[j] = this$0.getPopupMenu();
                    MenuSelectionManager.defaultManager().setSelectedPath(me);
                }
            }
        }
    }
    
    public void selectAllAccessibleSelection() {
    }
}
