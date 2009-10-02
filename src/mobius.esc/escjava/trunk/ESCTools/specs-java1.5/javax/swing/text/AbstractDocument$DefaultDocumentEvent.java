package javax.swing.text;

import java.util.*;
import java.io.*;
import javax.swing.UIManager;
import javax.swing.undo.*;
import javax.swing.event.*;

public class AbstractDocument$DefaultDocumentEvent extends CompoundEdit implements DocumentEvent {
    
    /*synthetic*/ static DocumentEvent$EventType access$100(AbstractDocument$DefaultDocumentEvent x0) {
        return x0.type;
    }
    /*synthetic*/ final AbstractDocument this$0;
    
    public AbstractDocument$DefaultDocumentEvent(/*synthetic*/ final AbstractDocument this$0, int offs, int len, DocumentEvent$EventType type) {
        this.this$0 = this$0;
        
        offset = offs;
        length = len;
        this.type = type;
    }
    
    public String toString() {
        return edits.toString();
    }
    
    public boolean addEdit(UndoableEdit anEdit) {
        if ((changeLookup == null) && (edits.size() > 10)) {
            changeLookup = new Hashtable();
            int n = edits.size();
            for (int i = 0; i < n; i++) {
                Object o = edits.elementAt(i);
                if (o instanceof DocumentEvent$ElementChange) {
                    DocumentEvent$ElementChange ec = (DocumentEvent$ElementChange)(DocumentEvent$ElementChange)o;
                    changeLookup.put(ec.getElement(), ec);
                }
            }
        }
        if ((changeLookup != null) && (anEdit instanceof DocumentEvent$ElementChange)) {
            DocumentEvent$ElementChange ec = (DocumentEvent$ElementChange)(DocumentEvent$ElementChange)anEdit;
            changeLookup.put(ec.getElement(), ec);
        }
        return super.addEdit(anEdit);
    }
    
    public void redo() throws CannotRedoException {
        this$0.writeLock();
        try {
            super.redo();
            AbstractDocument$UndoRedoDocumentEvent ev = new AbstractDocument$UndoRedoDocumentEvent(this$0, this, false);
            if (type == DocumentEvent$EventType.INSERT) {
                this$0.fireInsertUpdate(ev);
            } else if (type == DocumentEvent$EventType.REMOVE) {
                this$0.fireRemoveUpdate(ev);
            } else {
                this$0.fireChangedUpdate(ev);
            }
        } finally {
            this$0.writeUnlock();
        }
    }
    
    public void undo() throws CannotUndoException {
        this$0.writeLock();
        try {
            super.undo();
            AbstractDocument$UndoRedoDocumentEvent ev = new AbstractDocument$UndoRedoDocumentEvent(this$0, this, true);
            if (type == DocumentEvent$EventType.REMOVE) {
                this$0.fireInsertUpdate(ev);
            } else if (type == DocumentEvent$EventType.INSERT) {
                this$0.fireRemoveUpdate(ev);
            } else {
                this$0.fireChangedUpdate(ev);
            }
        } finally {
            this$0.writeUnlock();
        }
    }
    
    public boolean isSignificant() {
        return true;
    }
    
    public String getPresentationName() {
        DocumentEvent$EventType type = getType();
        if (type == DocumentEvent$EventType.INSERT) return UIManager.getString("AbstractDocument.additionText");
        if (type == DocumentEvent$EventType.REMOVE) return UIManager.getString("AbstractDocument.deletionText");
        return UIManager.getString("AbstractDocument.styleChangeText");
    }
    
    public String getUndoPresentationName() {
        return UIManager.getString("AbstractDocument.undoText") + " " + getPresentationName();
    }
    
    public String getRedoPresentationName() {
        return UIManager.getString("AbstractDocument.redoText") + " " + getPresentationName();
    }
    
    public DocumentEvent$EventType getType() {
        return type;
    }
    
    public int getOffset() {
        return offset;
    }
    
    public int getLength() {
        return length;
    }
    
    public Document getDocument() {
        return this$0;
    }
    
    public DocumentEvent$ElementChange getChange(Element elem) {
        if (changeLookup != null) {
            return (DocumentEvent$ElementChange)(DocumentEvent$ElementChange)changeLookup.get(elem);
        }
        int n = edits.size();
        for (int i = 0; i < n; i++) {
            Object o = edits.elementAt(i);
            if (o instanceof DocumentEvent$ElementChange) {
                DocumentEvent$ElementChange c = (DocumentEvent$ElementChange)(DocumentEvent$ElementChange)o;
                if (elem.equals(c.getElement())) {
                    return c;
                }
            }
        }
        return null;
    }
    private int offset;
    private int length;
    private Hashtable changeLookup;
    private DocumentEvent$EventType type;
}
