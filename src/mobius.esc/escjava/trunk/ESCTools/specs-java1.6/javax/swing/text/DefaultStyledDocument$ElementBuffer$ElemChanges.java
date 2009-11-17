package javax.swing.text;

import java.util.Vector;
import javax.swing.event.*;

class DefaultStyledDocument$ElementBuffer$ElemChanges {
    /*synthetic*/ final DefaultStyledDocument$ElementBuffer this$1;
    
    DefaultStyledDocument$ElementBuffer$ElemChanges(/*synthetic*/ final DefaultStyledDocument$ElementBuffer this$1, Element parent, int index, boolean isFracture) {
        this.this$1 = this$1;
        
        this.parent = parent;
        this.index = index;
        this.isFracture = isFracture;
        added = new Vector();
        removed = new Vector();
    }
    
    public String toString() {
        return "added: " + added + "\nremoved: " + removed + "\n";
    }
    Element parent;
    int index;
    Vector added;
    Vector removed;
    boolean isFracture;
}
