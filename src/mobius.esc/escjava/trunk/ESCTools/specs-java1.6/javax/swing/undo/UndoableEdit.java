package javax.swing.undo;

import javax.swing.event.*;

public interface UndoableEdit {
    
    public void undo() throws CannotUndoException;
    
    public boolean canUndo();
    
    public void redo() throws CannotRedoException;
    
    public boolean canRedo();
    
    public void die();
    
    public boolean addEdit(UndoableEdit anEdit);
    
    public boolean replaceEdit(UndoableEdit anEdit);
    
    public boolean isSignificant();
    
    public String getPresentationName();
    
    public String getUndoPresentationName();
    
    public String getRedoPresentationName();
}
