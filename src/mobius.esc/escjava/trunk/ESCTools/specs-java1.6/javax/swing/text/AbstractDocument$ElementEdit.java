package javax.swing.text;

import java.util.*;
import java.io.*;
import javax.swing.undo.*;
import javax.swing.event.*;

public class AbstractDocument$ElementEdit extends AbstractUndoableEdit implements DocumentEvent$ElementChange {
    
    public AbstractDocument$ElementEdit(Element e, int index, Element[] removed, Element[] added) {
        
        this.e = e;
        this.index = index;
        this.removed = removed;
        this.added = added;
    }
    
    public Element getElement() {
        return e;
    }
    
    public int getIndex() {
        return index;
    }
    
    public Element[] getChildrenRemoved() {
        return removed;
    }
    
    public Element[] getChildrenAdded() {
        return added;
    }
    
    public void redo() throws CannotRedoException {
        super.redo();
        Element[] tmp = removed;
        removed = added;
        added = tmp;
        ((AbstractDocument$BranchElement)(AbstractDocument$BranchElement)e).replace(index, removed.length, added);
    }
    
    public void undo() throws CannotUndoException {
        super.undo();
        ((AbstractDocument$BranchElement)(AbstractDocument$BranchElement)e).replace(index, added.length, removed);
        Element[] tmp = removed;
        removed = added;
        added = tmp;
    }
    private Element e;
    private int index;
    private Element[] removed;
    private Element[] added;
}
