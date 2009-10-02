package javax.swing.undo;

import java.util.*;

public class CompoundEdit extends AbstractUndoableEdit {
    boolean inProgress;
    protected Vector edits;
    
    public CompoundEdit() {
        
        inProgress = true;
        edits = new Vector();
    }
    
    public void undo() throws CannotUndoException {
        super.undo();
        int i = edits.size();
        while (i-- > 0) {
            UndoableEdit e = (UndoableEdit)(UndoableEdit)edits.elementAt(i);
            e.undo();
        }
    }
    
    public void redo() throws CannotRedoException {
        super.redo();
        Enumeration cursor = edits.elements();
        while (cursor.hasMoreElements()) {
            ((UndoableEdit)(UndoableEdit)cursor.nextElement()).redo();
        }
    }
    
    protected UndoableEdit lastEdit() {
        int count = edits.size();
        if (count > 0) return (UndoableEdit)(UndoableEdit)edits.elementAt(count - 1); else return null;
    }
    
    public void die() {
        int size = edits.size();
        for (int i = size - 1; i >= 0; i--) {
            UndoableEdit e = (UndoableEdit)(UndoableEdit)edits.elementAt(i);
            e.die();
        }
        super.die();
    }
    
    public boolean addEdit(UndoableEdit anEdit) {
        if (!inProgress) {
            return false;
        } else {
            UndoableEdit last = lastEdit();
            if (last == null) {
                edits.addElement(anEdit);
            } else if (!last.addEdit(anEdit)) {
                if (anEdit.replaceEdit(last)) {
                    edits.removeElementAt(edits.size() - 1);
                }
                edits.addElement(anEdit);
            }
            return true;
        }
    }
    
    public void end() {
        inProgress = false;
    }
    
    public boolean canUndo() {
        return !isInProgress() && super.canUndo();
    }
    
    public boolean canRedo() {
        return !isInProgress() && super.canRedo();
    }
    
    public boolean isInProgress() {
        return inProgress;
    }
    
    public boolean isSignificant() {
        Enumeration cursor = edits.elements();
        while (cursor.hasMoreElements()) {
            if (((UndoableEdit)(UndoableEdit)cursor.nextElement()).isSignificant()) {
                return true;
            }
        }
        return false;
    }
    
    public String getPresentationName() {
        UndoableEdit last = lastEdit();
        if (last != null) {
            return last.getPresentationName();
        } else {
            return super.getPresentationName();
        }
    }
    
    public String getUndoPresentationName() {
        UndoableEdit last = lastEdit();
        if (last != null) {
            return last.getUndoPresentationName();
        } else {
            return super.getUndoPresentationName();
        }
    }
    
    public String getRedoPresentationName() {
        UndoableEdit last = lastEdit();
        if (last != null) {
            return last.getRedoPresentationName();
        } else {
            return super.getRedoPresentationName();
        }
    }
    
    public String toString() {
        return super.toString() + " inProgress: " + inProgress + " edits: " + edits;
    }
}
