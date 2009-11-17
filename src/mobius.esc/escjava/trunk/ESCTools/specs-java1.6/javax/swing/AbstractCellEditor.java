package javax.swing;

import javax.swing.event.*;
import java.util.EventObject;
import java.io.Serializable;

public abstract class AbstractCellEditor implements CellEditor, Serializable {
    
    public AbstractCellEditor() {
        
    }
    protected EventListenerList listenerList = new EventListenerList();
    protected transient ChangeEvent changeEvent = null;
    
    public boolean isCellEditable(EventObject e) {
        return true;
    }
    
    public boolean shouldSelectCell(EventObject anEvent) {
        return true;
    }
    
    public boolean stopCellEditing() {
        fireEditingStopped();
        return true;
    }
    
    public void cancelCellEditing() {
        fireEditingCanceled();
    }
    
    public void addCellEditorListener(CellEditorListener l) {
        listenerList.add(CellEditorListener.class, l);
    }
    
    public void removeCellEditorListener(CellEditorListener l) {
        listenerList.remove(CellEditorListener.class, l);
    }
    
    public CellEditorListener[] getCellEditorListeners() {
        return (CellEditorListener[])(CellEditorListener[])listenerList.getListeners(CellEditorListener.class);
    }
    
    protected void fireEditingStopped() {
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == CellEditorListener.class) {
                if (changeEvent == null) changeEvent = new ChangeEvent(this);
                ((CellEditorListener)(CellEditorListener)listeners[i + 1]).editingStopped(changeEvent);
            }
        }
    }
    
    protected void fireEditingCanceled() {
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == CellEditorListener.class) {
                if (changeEvent == null) changeEvent = new ChangeEvent(this);
                ((CellEditorListener)(CellEditorListener)listeners[i + 1]).editingCanceled(changeEvent);
            }
        }
    }
}
