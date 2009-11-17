package javax.swing.plaf.basic;

import javax.swing.*;
import java.awt.*;
import java.awt.event.*;
import java.lang.reflect.Method;

public class BasicComboBoxEditor implements ComboBoxEditor, FocusListener {
    protected JTextField editor;
    private Object oldValue;
    
    public BasicComboBoxEditor() {
        
        editor = new BasicComboBoxEditor$BorderlessTextField("", 9);
        editor.setBorder(null);
    }
    
    public Component getEditorComponent() {
        return editor;
    }
    
    public void setItem(Object anObject) {
        if (anObject != null) {
            editor.setText(anObject.toString());
            oldValue = anObject;
        } else {
            editor.setText("");
        }
    }
    
    public Object getItem() {
        Object newValue = editor.getText();
        if (oldValue != null && !(oldValue instanceof String)) {
            if (newValue.equals(oldValue.toString())) {
                return oldValue;
            } else {
                Class cls = oldValue.getClass();
                try {
                    Method method = cls.getMethod("valueOf", new Class[]{String.class});
                    newValue = method.invoke(oldValue, new Object[]{editor.getText()});
                } catch (Exception ex) {
                }
            }
        }
        return newValue;
    }
    
    public void selectAll() {
        editor.selectAll();
        editor.requestFocus();
    }
    
    public void focusGained(FocusEvent e) {
    }
    
    public void focusLost(FocusEvent e) {
    }
    
    public void addActionListener(ActionListener l) {
        editor.addActionListener(l);
    }
    
    public void removeActionListener(ActionListener l) {
        editor.removeActionListener(l);
    }
    {
    }
    {
    }
}
