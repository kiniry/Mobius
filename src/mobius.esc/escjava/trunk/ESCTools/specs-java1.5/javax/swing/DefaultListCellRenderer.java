package javax.swing;

import javax.swing.*;
import javax.swing.event.*;
import javax.swing.border.*;
import java.awt.Component;
import java.awt.Color;
import java.awt.Rectangle;
import java.io.Serializable;

public class DefaultListCellRenderer extends JLabel implements ListCellRenderer, Serializable {
    protected static Border noFocusBorder = new EmptyBorder(1, 1, 1, 1);
    private static final Border SAFE_NO_FOCUS_BORDER = new EmptyBorder(1, 1, 1, 1);
    
    public DefaultListCellRenderer() {
        
        setOpaque(true);
        setBorder(getNoFocusBorder());
    }
    
    private static Border getNoFocusBorder() {
        if (System.getSecurityManager() != null) {
            return SAFE_NO_FOCUS_BORDER;
        } else {
            return noFocusBorder;
        }
    }
    
    public Component getListCellRendererComponent(JList list, Object value, int index, boolean isSelected, boolean cellHasFocus) {
        setComponentOrientation(list.getComponentOrientation());
        if (isSelected) {
            setBackground(list.getSelectionBackground());
            setForeground(list.getSelectionForeground());
        } else {
            setBackground(list.getBackground());
            setForeground(list.getForeground());
        }
        if (value instanceof Icon) {
            setIcon((Icon)(Icon)value);
            setText("");
        } else {
            setIcon(null);
            setText((value == null) ? "" : value.toString());
        }
        setEnabled(list.isEnabled());
        setFont(list.getFont());
        Border border = null;
        if (cellHasFocus) {
            if (isSelected) {
                border = UIManager.getBorder("List.focusSelectedCellHighlightBorder");
            }
            if (border == null) {
                border = UIManager.getBorder("List.focusCellHighlightBorder");
            }
        } else {
            border = getNoFocusBorder();
        }
        setBorder(border);
        return this;
    }
    
    public boolean isOpaque() {
        Color back = getBackground();
        Component p = getParent();
        if (p != null) {
            p = p.getParent();
        }
        boolean colorMatch = (back != null) && (p != null) && back.equals(p.getBackground()) && p.isOpaque();
        return !colorMatch && super.isOpaque();
    }
    
    public void validate() {
    }
    
    public void invalidate() {
    }
    
    public void repaint() {
    }
    
    public void revalidate() {
    }
    
    public void repaint(long tm, int x, int y, int width, int height) {
    }
    
    public void repaint(Rectangle r) {
    }
    
    protected void firePropertyChange(String propertyName, Object oldValue, Object newValue) {
        if (propertyName == "text") super.firePropertyChange(propertyName, oldValue, newValue);
    }
    
    public void firePropertyChange(String propertyName, byte oldValue, byte newValue) {
    }
    
    public void firePropertyChange(String propertyName, char oldValue, char newValue) {
    }
    
    public void firePropertyChange(String propertyName, short oldValue, short newValue) {
    }
    
    public void firePropertyChange(String propertyName, int oldValue, int newValue) {
    }
    
    public void firePropertyChange(String propertyName, long oldValue, long newValue) {
    }
    
    public void firePropertyChange(String propertyName, float oldValue, float newValue) {
    }
    
    public void firePropertyChange(String propertyName, double oldValue, double newValue) {
    }
    
    public void firePropertyChange(String propertyName, boolean oldValue, boolean newValue) {
    }
    {
    }
}
