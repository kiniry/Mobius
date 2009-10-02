package javax.swing.table;

import javax.swing.*;
import javax.swing.table.TableCellRenderer;
import javax.swing.border.*;
import java.awt.Component;
import java.awt.Color;
import java.awt.Rectangle;
import java.io.Serializable;

public class DefaultTableCellRenderer extends JLabel implements TableCellRenderer, Serializable {
    protected static Border noFocusBorder = new EmptyBorder(1, 1, 1, 1);
    private static final Border SAFE_NO_FOCUS_BORDER = new EmptyBorder(1, 1, 1, 1);
    private Color unselectedForeground;
    private Color unselectedBackground;
    
    public DefaultTableCellRenderer() {
        
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
    
    public void setForeground(Color c) {
        super.setForeground(c);
        unselectedForeground = c;
    }
    
    public void setBackground(Color c) {
        super.setBackground(c);
        unselectedBackground = c;
    }
    
    public void updateUI() {
        super.updateUI();
        setForeground(null);
        setBackground(null);
    }
    
    public Component getTableCellRendererComponent(JTable table, Object value, boolean isSelected, boolean hasFocus, int row, int column) {
        if (isSelected) {
            super.setForeground(table.getSelectionForeground());
            super.setBackground(table.getSelectionBackground());
        } else {
            super.setForeground((unselectedForeground != null) ? unselectedForeground : table.getForeground());
            super.setBackground((unselectedBackground != null) ? unselectedBackground : table.getBackground());
        }
        setFont(table.getFont());
        if (hasFocus) {
            Border border = null;
            if (isSelected) {
                border = UIManager.getBorder("Table.focusSelectedCellHighlightBorder");
            }
            if (border == null) {
                border = UIManager.getBorder("Table.focusCellHighlightBorder");
            }
            setBorder(border);
            if (!isSelected && table.isCellEditable(row, column)) {
                Color col;
                col = UIManager.getColor("Table.focusCellForeground");
                if (col != null) {
                    super.setForeground(col);
                }
                col = UIManager.getColor("Table.focusCellBackground");
                if (col != null) {
                    super.setBackground(col);
                }
            }
        } else {
            setBorder(getNoFocusBorder());
        }
        setValue(value);
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
    
    public void invalidate() {
    }
    
    public void validate() {
    }
    
    public void revalidate() {
    }
    
    public void repaint(long tm, int x, int y, int width, int height) {
    }
    
    public void repaint(Rectangle r) {
    }
    
    public void repaint() {
    }
    
    protected void firePropertyChange(String propertyName, Object oldValue, Object newValue) {
        if (propertyName == "text") {
            super.firePropertyChange(propertyName, oldValue, newValue);
        }
    }
    
    public void firePropertyChange(String propertyName, boolean oldValue, boolean newValue) {
    }
    
    protected void setValue(Object value) {
        setText((value == null) ? "" : value.toString());
    }
    {
    }
}
