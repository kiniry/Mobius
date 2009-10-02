package javax.swing.event;

import javax.swing.undo.*;
import javax.swing.text.*;

public interface DocumentEvent {
    
    public int getOffset();
    
    public int getLength();
    
    public Document getDocument();
    
    public DocumentEvent$EventType getType();
    
    public DocumentEvent$ElementChange getChange(Element elem);
    {
    }
    {
    }
}
