package javax.swing.text;

import java.util.*;
import java.io.*;
import javax.swing.undo.*;
import javax.swing.event.*;

public class AbstractDocument$LeafElement extends AbstractDocument$AbstractElement {
    /*synthetic*/ final AbstractDocument this$0;
    
    public AbstractDocument$LeafElement(/*synthetic*/ final AbstractDocument this$0, Element parent, AttributeSet a, int offs0, int offs1) {
        super(this$0, parent, a);
        this.this$0 = this$0;
        try {
            p0 = this$0.createPosition(offs0);
            p1 = this$0.createPosition(offs1);
        } catch (BadLocationException e) {
            p0 = null;
            p1 = null;
            throw new StateInvariantError("Can\'t create Position references");
        }
    }
    
    public String toString() {
        return "LeafElement(" + getName() + ") " + p0 + "," + p1 + "\n";
    }
    
    public int getStartOffset() {
        return p0.getOffset();
    }
    
    public int getEndOffset() {
        return p1.getOffset();
    }
    
    public String getName() {
        String nm = super.getName();
        if (nm == null) {
            nm = "content";
        }
        return nm;
    }
    
    public int getElementIndex(int pos) {
        return -1;
    }
    
    public Element getElement(int index) {
        return null;
    }
    
    public int getElementCount() {
        return 0;
    }
    
    public boolean isLeaf() {
        return true;
    }
    
    public boolean getAllowsChildren() {
        return false;
    }
    
    public Enumeration children() {
        return null;
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        s.writeInt(p0.getOffset());
        s.writeInt(p1.getOffset());
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException {
        s.defaultReadObject();
        int off0 = s.readInt();
        int off1 = s.readInt();
        try {
            p0 = this$0.createPosition(off0);
            p1 = this$0.createPosition(off1);
        } catch (BadLocationException e) {
            p0 = null;
            p1 = null;
            throw new IOException("Can\'t restore Position references");
        }
    }
    private transient Position p0;
    private transient Position p1;
}
