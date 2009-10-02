package javax.swing.event;

import javax.swing.undo.*;

public interface UndoableEditListener extends java.util.EventListener {
    
    void undoableEditHappened(UndoableEditEvent e);
}
