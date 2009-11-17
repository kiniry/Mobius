package javax.swing;

import java.awt.event.*;
import javax.swing.table.*;
import javax.swing.event.*;
import javax.swing.tree.*;

class DefaultCellEditor$1 extends DefaultCellEditor$EditorDelegate {
    /*synthetic*/ final DefaultCellEditor this$0;
    /*synthetic*/ final JTextField val$textField;
    
    DefaultCellEditor$1(/*synthetic*/ final DefaultCellEditor this$0, /*synthetic*/ final JTextField val$textField) {
        super(this$0);
        this.this$0 = this$0;
        this.val$textField = val$textField;
    }
    
    public void setValue(Object value) {
        val$textField.setText((value != null) ? value.toString() : "");
    }
    
    public Object getCellEditorValue() {
        return val$textField.getText();
    }
}
