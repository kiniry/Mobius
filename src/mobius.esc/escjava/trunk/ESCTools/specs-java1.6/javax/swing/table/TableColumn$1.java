package javax.swing.table;

import javax.swing.*;
import javax.swing.border.*;
import java.awt.Component;

class TableColumn$1 extends DefaultTableCellRenderer {
    /*synthetic*/ final TableColumn this$0;
    
    TableColumn$1(/*synthetic*/ final TableColumn this$0) {
        this.this$0 = this$0;
        
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
