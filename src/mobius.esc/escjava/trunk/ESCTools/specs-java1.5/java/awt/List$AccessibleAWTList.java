package java.awt;

import java.awt.event.*;
import javax.accessibility.*;

public class List$AccessibleAWTList extends Component$AccessibleAWTComponent implements AccessibleSelection, ItemListener, ActionListener {
    /*synthetic*/ final List this$0;
    private static final long serialVersionUID = 7924617370136012829L;
    
    public List$AccessibleAWTList(/*synthetic*/ final List this$0) {
        this.this$0 = this$0;
        super(this$0);
        this$0.addActionListener(this);
        this$0.addItemListener(this);
    }
    
    public void actionPerformed(ActionEvent event) {
    }
    
    public void itemStateChanged(ItemEvent event) {
    }
    
    public AccessibleStateSet getAccessibleStateSet() {
        AccessibleStateSet states = super.getAccessibleStateSet();
        if (this$0.isMultipleMode()) {
            states.add(AccessibleState.MULTISELECTABLE);
        }
        return states;
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.LIST;
    }
    
    public Accessible getAccessibleAt(Point p) {
        return null;
    }
    
    public int getAccessibleChildrenCount() {
        return this$0.getItemCount();
    }
    
    public Accessible getAccessibleChild(int i) {
        synchronized (this$0) {
            if (i >= this$0.getItemCount()) {
                return null;
            } else {
                return new List$AccessibleAWTList$AccessibleAWTListChild(this, this$0, i);
            }
        }
    }
    
    public AccessibleSelection getAccessibleSelection() {
        return this;
    }
    
    public int getAccessibleSelectionCount() {
        return this$0.getSelectedIndexes().length;
    }
    
    public Accessible getAccessibleSelection(int i) {
        synchronized (this$0) {
            int len = getAccessibleSelectionCount();
            if (i < 0 || i >= len) {
                return null;
            } else {
                return getAccessibleChild(this$0.getSelectedIndexes()[i]);
            }
        }
    }
    
    public boolean isAccessibleChildSelected(int i) {
        return this$0.isIndexSelected(i);
    }
    
    public void addAccessibleSelection(int i) {
        this$0.select(i);
    }
    
    public void removeAccessibleSelection(int i) {
        this$0.deselect(i);
    }
    
    public void clearAccessibleSelection() {
        synchronized (this$0) {
            int[] selectedIndexes = this$0.getSelectedIndexes();
            if (selectedIndexes == null) return;
            for (int i = selectedIndexes.length - 1; i >= 0; i--) {
                this$0.deselect(selectedIndexes[i]);
            }
        }
    }
    
    public void selectAllAccessibleSelection() {
        synchronized (this$0) {
            for (int i = this$0.getItemCount() - 1; i >= 0; i--) {
                this$0.select(i);
            }
        }
    }
    {
    }
}
