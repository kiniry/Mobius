package javax.swing;

import java.awt.event.*;
import java.lang.Boolean;
import javax.swing.table.*;
import javax.swing.event.*;
import javax.swing.tree.*;

class DefaultCellEditor$2 extends DefaultCellEditor$EditorDelegate {
    /*synthetic*/ final DefaultCellEditor this$0;
    /*synthetic*/ final JCheckBox val$checkBox;
    
    DefaultCellEditor$2(/*synthetic*/ final DefaultCellEditor this$0, /*synthetic*/ final JCheckBox val$checkBox) {
        this.this$0 = this$0;
        this.val$checkBox = val$checkBox;
        super(this$0);
    }
    
    public void setValue(Object value) {
        boolean selected = false;
        if (value instanceof Boolean) {
            selected = ((Boolean)(Boolean)value).booleanValue();
        } else if (value instanceof String) {
            selected = value.equals("true");
        }
        val$checkBox.setSelected(selected);
    }
    
    public Object getCellEditorValue() {
        return Boolean.valueOf(val$checkBox.isSelected());
    }
}
