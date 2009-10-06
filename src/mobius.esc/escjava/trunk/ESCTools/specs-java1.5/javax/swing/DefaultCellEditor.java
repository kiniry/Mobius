package javax.swing;

import java.awt.Component;
import java.awt.event.*;
import java.lang.Boolean;
import javax.swing.table.*;
import javax.swing.event.*;
import java.util.EventObject;
import javax.swing.tree.*;

public class DefaultCellEditor extends AbstractCellEditor implements TableCellEditor, TreeCellEditor {
    protected JComponent editorComponent;
    protected DefaultCellEditor$EditorDelegate delegate;
    protected int clickCountToStart = 1;
    
    public DefaultCellEditor(final JTextField textField) {
        
        editorComponent = textField;
        this.clickCountToStart = 2;
        delegate = new DefaultCellEditor$1(this, textField);
        textField.addActionListener(delegate);
    }
    
    public DefaultCellEditor(final JCheckBox checkBox) {
        
        editorComponent = checkBox;
        delegate = new DefaultCellEditor$2(this, checkBox);
        checkBox.addActionListener(delegate);
        if (com.sun.java.swing.SwingUtilities2.DRAG_FIX) {
            checkBox.setRequestFocusEnabled(false);
        }
    }
    
    public DefaultCellEditor(final JComboBox comboBox) {
        
        editorComponent = comboBox;
        comboBox.putClientProperty("JComboBox.isTableCellEditor", Boolean.TRUE);
        delegate = new DefaultCellEditor$3(this, comboBox);
        comboBox.addActionListener(delegate);
    }
    
    public Component getComponent() {
        return editorComponent;
    }
    
    public void setClickCountToStart(int count) {
        clickCountToStart = count;
    }
    
    public int getClickCountToStart() {
        return clickCountToStart;
    }
    
    public Object getCellEditorValue() {
        return delegate.getCellEditorValue();
    }
    
    public boolean isCellEditable(EventObject anEvent) {
        return delegate.isCellEditable(anEvent);
    }
    
    public boolean shouldSelectCell(EventObject anEvent) {
        return delegate.shouldSelectCell(anEvent);
    }
    
    public boolean stopCellEditing() {
        return delegate.stopCellEditing();
    }
    
    public void cancelCellEditing() {
        delegate.cancelCellEditing();
    }
    
    public Component getTreeCellEditorComponent(JTree tree, Object value, boolean isSelected, boolean expanded, boolean leaf, int row) {
        String stringValue = tree.convertValueToText(value, isSelected, expanded, leaf, row, false);
        delegate.setValue(stringValue);
        return editorComponent;
    }
    
    public Component getTableCellEditorComponent(JTable table, Object value, boolean isSelected, int row, int column) {
        delegate.setValue(value);
        return editorComponent;
    }
    {
    }
}
