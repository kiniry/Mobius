package javax.swing.table;

import java.util.*;
import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

class JTableHeader$UIResourceTableCellRenderer extends DefaultTableCellRenderer implements UIResource {
    
    /*synthetic*/ JTableHeader$UIResourceTableCellRenderer(javax.swing.table.JTableHeader$1 x0) {
        this();
    }
    
    private JTableHeader$UIResourceTableCellRenderer() {
        
    }
    
    public Component getTableCellRendererComponent(JTable table, Object value, boolean isSelected, boolean hasFocus, int row, int column) {
        if (table != null) {
            JTableHeader header = table.getTableHeader();
            if (header != null) {
                setForeground(header.getForeground());
                setBackground(header.getBackground());
                setFont(header.getFont());
            }
        }
        setText((value == null) ? "" : value.toString());
        setBorder(UIManager.getBorder("TableHeader.cellBorder"));
        return this;
    }
}
