package javax.swing;

import java.awt.event.*;
import javax.swing.table.*;
import javax.swing.event.*;
import java.util.EventObject;
import javax.swing.tree.*;

class DefaultCellEditor$3 extends DefaultCellEditor$EditorDelegate {
    /*synthetic*/ final DefaultCellEditor this$0;
    /*synthetic*/ final JComboBox val$comboBox;
    
    DefaultCellEditor$3(/*synthetic*/ final DefaultCellEditor this$0, /*synthetic*/ final JComboBox val$comboBox) {
        super(this$0);
        this.this$0 = this$0;
        this.val$comboBox = val$comboBox;
    }
    
    public void setValue(Object value) {
        val$comboBox.setSelectedItem(value);
    }
    
    public Object getCellEditorValue() {
        return val$comboBox.getSelectedItem();
    }
    
    public boolean shouldSelectCell(EventObject anEvent) {
        if (anEvent instanceof MouseEvent) {
            MouseEvent e = (MouseEvent)(MouseEvent)anEvent;
            return e.getID() != MouseEvent.MOUSE_DRAGGED;
        }
        return true;
    }
    
    public boolean stopCellEditing() {
        if (val$comboBox.isEditable()) {
            val$comboBox.actionPerformed(new ActionEvent(this$0, 0, ""));
        }
        return super.stopCellEditing();
    }
}
