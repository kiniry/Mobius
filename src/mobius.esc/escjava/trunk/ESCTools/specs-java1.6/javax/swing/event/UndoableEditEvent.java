package javax.swing.event;

import javax.swing.undo.*;

public class UndoableEditEvent extends java.util.EventObject {
    private UndoableEdit myEdit;
    
    public UndoableEditEvent(Object source, UndoableEdit edit) {
        super(source);
        myEdit = edit;
    }
    
    public UndoableEdit getEdit() {
        return myEdit;
    }
}
