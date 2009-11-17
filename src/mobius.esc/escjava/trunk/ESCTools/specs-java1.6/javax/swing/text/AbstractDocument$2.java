package javax.swing.text;

import java.util.*;
import java.io.*;
import javax.swing.undo.*;
import javax.swing.event.*;

class AbstractDocument$2 implements ObjectInputValidation {
    /*synthetic*/ final AbstractDocument this$0;
    
    AbstractDocument$2(/*synthetic*/ final AbstractDocument this$0) {
        this.this$0 = this$0;
        
    }
    
    public void validateObject() {
        try {
            this$0.writeLock();
            AbstractDocument$DefaultDocumentEvent e = new AbstractDocument$DefaultDocumentEvent(this$0, 0, this$0.getLength(), DocumentEvent$EventType.INSERT);
            this$0.updateBidi(e);
        } finally {
            this$0.writeUnlock();
        }
    }
}
