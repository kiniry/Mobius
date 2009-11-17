package javax.swing.event;

import javax.swing.undo.*;
import javax.swing.text.*;

public final class DocumentEvent$EventType {
    
    private DocumentEvent$EventType(String s) {
        
        typeString = s;
    }
    public static final DocumentEvent$EventType INSERT = new DocumentEvent$EventType("INSERT");
    public static final DocumentEvent$EventType REMOVE = new DocumentEvent$EventType("REMOVE");
    public static final DocumentEvent$EventType CHANGE = new DocumentEvent$EventType("CHANGE");
    
    public String toString() {
        return typeString;
    }
    private String typeString;
}
