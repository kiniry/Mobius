package javax.swing;

import java.util.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.print.*;
import java.beans.*;
import javax.accessibility.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.table.*;
import javax.swing.border.*;
import javax.print.attribute.*;

class JTable$GenericEditor extends DefaultCellEditor {
    Class[] argTypes = new Class[]{String.class};
    java.lang.reflect.Constructor constructor;
    Object value;
    
    public JTable$GenericEditor() {
        super(new JTextField());
        getComponent().setName("Table.editor");
    }
    
    public boolean stopCellEditing() {
        String s = (String)(String)super.getCellEditorValue();
        if ("".equals(s)) {
            if (constructor.getDeclaringClass() == String.class) {
                value = s;
            }
            super.stopCellEditing();
        }
        try {
            value = constructor.newInstance(new Object[]{s});
        } catch (Exception e) {
            ((JComponent)(JComponent)getComponent()).setBorder(new LineBorder(Color.red));
            return false;
        }
        return super.stopCellEditing();
    }
    
    public Component getTableCellEditorComponent(JTable table, Object value, boolean isSelected, int row, int column) {
        this.value = null;
        ((JComponent)(JComponent)getComponent()).setBorder(new LineBorder(Color.black));
        try {
            Class type = table.getColumnClass(column);
            if (type == Object.class) {
                type = String.class;
            }
            constructor = type.getConstructor(argTypes);
        } catch (Exception e) {
            return null;
        }
        return super.getTableCellEditorComponent(table, value, isSelected, row, column);
    }
    
    public Object getCellEditorValue() {
        return value;
    }
}
