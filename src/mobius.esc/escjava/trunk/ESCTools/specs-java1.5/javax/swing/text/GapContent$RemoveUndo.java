package javax.swing.text;

import java.util.Vector;
import javax.swing.undo.AbstractUndoableEdit;
import javax.swing.undo.CannotRedoException;
import javax.swing.undo.CannotUndoException;

class GapContent$RemoveUndo extends AbstractUndoableEdit {
    /*synthetic*/ final GapContent this$0;
    
    protected GapContent$RemoveUndo(/*synthetic*/ final GapContent this$0, int offset, String string) {
        this.this$0 = this$0;
        
        this.offset = offset;
        this.string = string;
        this.length = string.length();
        posRefs = this$0.getPositionsInRange(null, offset, length);
    }
    
    public void undo() throws CannotUndoException {
        super.undo();
        try {
            this$0.insertString(offset, string);
            if (posRefs != null) {
                this$0.updateUndoPositions(posRefs, offset, length);
                posRefs = null;
            }
            string = null;
        } catch (BadLocationException bl) {
            throw new CannotUndoException();
        }
    }
    
    public void redo() throws CannotRedoException {
        super.redo();
        try {
            string = this$0.getString(offset, length);
            posRefs = this$0.getPositionsInRange(null, offset, length);
            this$0.remove(offset, length);
        } catch (BadLocationException bl) {
            throw new CannotRedoException();
        }
    }
    protected int offset;
    protected int length;
    protected String string;
    protected Vector posRefs;
}
