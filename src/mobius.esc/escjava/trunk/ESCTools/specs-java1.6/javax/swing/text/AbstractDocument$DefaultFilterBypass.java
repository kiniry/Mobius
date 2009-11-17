package javax.swing.text;

import java.util.*;
import java.io.*;
import javax.swing.undo.*;
import javax.swing.event.*;

class AbstractDocument$DefaultFilterBypass extends DocumentFilter$FilterBypass {
    
    /*synthetic*/ AbstractDocument$DefaultFilterBypass(AbstractDocument x0, javax.swing.text.AbstractDocument$1 x1) {
        this(x0);
    }
    /*synthetic*/ final AbstractDocument this$0;
    
    private AbstractDocument$DefaultFilterBypass(/*synthetic*/ final AbstractDocument this$0) {
        this.this$0 = this$0;
        
    }
    
    public Document getDocument() {
        return this$0;
    }
    
    public void remove(int offset, int length) throws BadLocationException {
        this$0.handleRemove(offset, length);
    }
    
    public void insertString(int offset, String string, AttributeSet attr) throws BadLocationException {
        this$0.handleInsertString(offset, string, attr);
    }
    
    public void replace(int offset, int length, String text, AttributeSet attrs) throws BadLocationException {
        this$0.handleRemove(offset, length);
        this$0.handleInsertString(offset, text, attrs);
    }
}
