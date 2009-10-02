package javax.swing.text;

import javax.swing.event.*;
import javax.swing.undo.AbstractUndoableEdit;
import javax.swing.undo.CannotRedoException;
import javax.swing.undo.CannotUndoException;

class DefaultStyledDocument$StyleChangeUndoableEdit extends AbstractUndoableEdit {
    
    public DefaultStyledDocument$StyleChangeUndoableEdit(AbstractDocument$AbstractElement element, Style newStyle) {
        
        this.element = element;
        this.newStyle = newStyle;
        oldStyle = element.getResolveParent();
    }
    
    public void redo() throws CannotRedoException {
        super.redo();
        element.setResolveParent(newStyle);
    }
    
    public void undo() throws CannotUndoException {
        super.undo();
        element.setResolveParent(oldStyle);
    }
    protected AbstractDocument$AbstractElement element;
    protected Style newStyle;
    protected AttributeSet oldStyle;
}
