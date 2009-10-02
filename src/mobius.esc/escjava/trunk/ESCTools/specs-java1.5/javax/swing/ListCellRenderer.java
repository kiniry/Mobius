package javax.swing;

import java.awt.Component;

public interface ListCellRenderer {
    
    Component getListCellRendererComponent(JList list, Object value, int index, boolean isSelected, boolean cellHasFocus);
}
