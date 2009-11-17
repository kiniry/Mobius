package javax.swing;

import java.util.EventObject;
import javax.swing.event.*;

public interface CellEditor {
    
    public Object getCellEditorValue();
    
    public boolean isCellEditable(EventObject anEvent);
    
    public boolean shouldSelectCell(EventObject anEvent);
    
    public boolean stopCellEditing();
    
    public void cancelCellEditing();
    
    public void addCellEditorListener(CellEditorListener l);
    
    public void removeCellEditorListener(CellEditorListener l);
}
