package javax.swing;

import java.awt.*;
import java.awt.event.*;

public interface ComboBoxEditor {
    
    public Component getEditorComponent();
    
    public void setItem(Object anObject);
    
    public Object getItem();
    
    public void selectAll();
    
    public void addActionListener(ActionListener l);
    
    public void removeActionListener(ActionListener l);
}
