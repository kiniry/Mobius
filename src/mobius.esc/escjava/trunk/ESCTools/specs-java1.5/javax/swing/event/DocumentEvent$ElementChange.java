package javax.swing.event;

import javax.swing.undo.*;
import javax.swing.text.*;

public interface DocumentEvent$ElementChange {
    
    public Element getElement();
    
    public int getIndex();
    
    public Element[] getChildrenRemoved();
    
    public Element[] getChildrenAdded();
}
