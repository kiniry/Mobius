package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.border.Border;
import java.awt.*;
import java.awt.event.*;

class BasicComboBoxEditor$BorderlessTextField extends JTextField {
    
    public BasicComboBoxEditor$BorderlessTextField(String value, int n) {
        super(value, n);
    }
    
    public void setText(String s) {
        if (getText().equals(s)) {
            return;
        }
        super.setText(s);
    }
    
    public void setBorder(Border b) {
    }
}
