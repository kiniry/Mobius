package javax.swing.table;

import java.util.*;
import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

public class JTableHeader$AccessibleJTableHeader extends JComponent$AccessibleJComponent {
    /*synthetic*/ final JTableHeader this$0;
    
    protected JTableHeader$AccessibleJTableHeader(/*synthetic*/ final JTableHeader this$0) {
        super(this$0);
        this.this$0 = this$0;
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.PANEL;
    }
    
    public Accessible getAccessibleAt(Point p) {
        int column;
        if ((column = this$0.columnAtPoint(p)) != -1) {
            TableColumn aColumn = this$0.columnModel.getColumn(column);
            TableCellRenderer renderer = aColumn.getHeaderRenderer();
            if (renderer == null) {
                if (JTableHeader.access$100(this$0) != null) {
                    renderer = JTableHeader.access$100(this$0);
                } else {
                    return null;
                }
            }
            Component component = renderer.getTableCellRendererComponent(this$0.getTable(), aColumn.getHeaderValue(), false, false, -1, column);
            return new JTableHeader$AccessibleJTableHeader$AccessibleJTableHeaderEntry(this, column, this$0, this$0.table);
        } else {
            return null;
        }
    }
    
    public int getAccessibleChildrenCount() {
        return this$0.columnModel.getColumnCount();
    }
    
    public Accessible getAccessibleChild(int i) {
        if (i < 0 || i >= getAccessibleChildrenCount()) {
            return null;
        } else {
            TableColumn aColumn = this$0.columnModel.getColumn(i);
            TableCellRenderer renderer = aColumn.getHeaderRenderer();
            if (renderer == null) {
                if (JTableHeader.access$100(this$0) != null) {
                    renderer = JTableHeader.access$100(this$0);
                } else {
                    return null;
                }
            }
            Component component = renderer.getTableCellRendererComponent(this$0.getTable(), aColumn.getHeaderValue(), false, false, -1, i);
            return new JTableHeader$AccessibleJTableHeader$AccessibleJTableHeaderEntry(this, i, this$0, this$0.table);
        }
    }
    {
    }
}
