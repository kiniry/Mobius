package javax.swing.text;

import javax.swing.event.*;
import javax.swing.undo.AbstractUndoableEdit;
import javax.swing.undo.CannotRedoException;
import javax.swing.undo.CannotUndoException;

public class DefaultStyledDocument$AttributeUndoableEdit extends AbstractUndoableEdit {
    
    public DefaultStyledDocument$AttributeUndoableEdit(Element element, AttributeSet newAttributes, boolean isReplacing) {
        
        this.element = element;
        this.newAttributes = newAttributes;
        this.isReplacing = isReplacing;
        copy = element.getAttributes().copyAttributes();
    }
    
    public void redo() throws CannotRedoException {
        super.redo();
        MutableAttributeSet as = (MutableAttributeSet)(MutableAttributeSet)element.getAttributes();
        if (isReplacing) as.removeAttributes(as);
        as.addAttributes(newAttributes);
    }
    
    public void undo() throws CannotUndoException {
        super.undo();
        MutableAttributeSet as = (MutableAttributeSet)(MutableAttributeSet)element.getAttributes();
        as.removeAttributes(as);
        as.addAttributes(copy);
    }
    protected AttributeSet newAttributes;
    protected AttributeSet copy;
    protected boolean isReplacing;
    protected Element element;
}
