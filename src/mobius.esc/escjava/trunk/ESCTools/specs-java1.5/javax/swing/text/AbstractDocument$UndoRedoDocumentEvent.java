package javax.swing.text;

import java.util.*;
import java.io.*;
import javax.swing.undo.*;
import javax.swing.event.*;

class AbstractDocument$UndoRedoDocumentEvent implements DocumentEvent {
    /*synthetic*/ final AbstractDocument this$0;
    private AbstractDocument$DefaultDocumentEvent src = null;
    private boolean isUndo;
    private DocumentEvent$EventType type = null;
    
    public AbstractDocument$UndoRedoDocumentEvent(/*synthetic*/ final AbstractDocument this$0, AbstractDocument$DefaultDocumentEvent src, boolean isUndo) {
        this.this$0 = this$0;
        
        this.src = src;
        this.isUndo = isUndo;
        if (isUndo) {
            if (src.getType().equals(DocumentEvent$EventType.INSERT)) {
                type = DocumentEvent$EventType.REMOVE;
            } else if (src.getType().equals(DocumentEvent$EventType.REMOVE)) {
                type = DocumentEvent$EventType.INSERT;
            } else {
                type = src.getType();
            }
        } else {
            type = src.getType();
        }
    }
    
    public AbstractDocument$DefaultDocumentEvent getSource() {
        return src;
    }
    
    public int getOffset() {
        return src.getOffset();
    }
    
    public int getLength() {
        return src.getLength();
    }
    
    public Document getDocument() {
        return src.getDocument();
    }
    
    public DocumentEvent$EventType getType() {
        return type;
    }
    
    public DocumentEvent$ElementChange getChange(Element elem) {
        return src.getChange(elem);
    }
}
