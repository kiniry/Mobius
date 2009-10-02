package javax.swing;

import java.awt.event.*;
import javax.swing.table.*;
import javax.swing.event.*;
import java.util.EventObject;
import javax.swing.tree.*;
import java.io.Serializable;

public class DefaultCellEditor$EditorDelegate implements ActionListener, ItemListener, Serializable {
    /*synthetic*/ final DefaultCellEditor this$0;
    
    protected DefaultCellEditor$EditorDelegate(/*synthetic*/ final DefaultCellEditor this$0) {
        this.this$0 = this$0;
        
    }
    protected Object value;
    
    public Object getCellEditorValue() {
        return value;
    }
    
    public void setValue(Object value) {
        this.value = value;
    }
    
    public boolean isCellEditable(EventObject anEvent) {
        if (anEvent instanceof MouseEvent) {
            return ((MouseEvent)(MouseEvent)anEvent).getClickCount() >= this$0.clickCountToStart;
        }
        return true;
    }
    
    public boolean shouldSelectCell(EventObject anEvent) {
        return true;
    }
    
    public boolean startCellEditing(EventObject anEvent) {
        return true;
    }
    
    public boolean stopCellEditing() {
        this$0.fireEditingStopped();
        return true;
    }
    
    public void cancelCellEditing() {
        this$0.fireEditingCanceled();
    }
    
    public void actionPerformed(ActionEvent e) {
        this$0.stopCellEditing();
    }
    
    public void itemStateChanged(ItemEvent e) {
        this$0.stopCellEditing();
    }
}
