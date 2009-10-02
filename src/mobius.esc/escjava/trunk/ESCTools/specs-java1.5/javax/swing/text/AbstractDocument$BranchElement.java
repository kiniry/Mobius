package javax.swing.text;

import java.util.*;
import java.io.*;
import javax.swing.undo.*;
import javax.swing.event.*;

public class AbstractDocument$BranchElement extends AbstractDocument$AbstractElement {
    /*synthetic*/ final AbstractDocument this$0;
    
    public AbstractDocument$BranchElement(/*synthetic*/ final AbstractDocument this$0, Element parent, AttributeSet a) {
        this.this$0 = this$0;
        super(this$0, parent, a);
        children = new AbstractDocument$AbstractElement[1];
        nchildren = 0;
        lastIndex = -1;
    }
    
    public Element positionToElement(int pos) {
        int index = getElementIndex(pos);
        Element child = children[index];
        int p0 = child.getStartOffset();
        int p1 = child.getEndOffset();
        if ((pos >= p0) && (pos < p1)) {
            return child;
        }
        return null;
    }
    
    public void replace(int offset, int length, Element[] elems) {
        int delta = elems.length - length;
        int src = offset + length;
        int nmove = nchildren - src;
        int dest = src + delta;
        if ((nchildren + delta) >= children.length) {
            int newLength = Math.max(2 * children.length, nchildren + delta);
            AbstractDocument$AbstractElement[] newChildren = new AbstractDocument$AbstractElement[newLength];
            System.arraycopy(children, 0, newChildren, 0, offset);
            System.arraycopy(elems, 0, newChildren, offset, elems.length);
            System.arraycopy(children, src, newChildren, dest, nmove);
            children = newChildren;
        } else {
            System.arraycopy(children, src, children, dest, nmove);
            System.arraycopy(elems, 0, children, offset, elems.length);
        }
        nchildren = nchildren + delta;
    }
    
    public String toString() {
        return "BranchElement(" + getName() + ") " + getStartOffset() + "," + getEndOffset() + "\n";
    }
    
    public String getName() {
        String nm = super.getName();
        if (nm == null) {
            nm = "paragraph";
        }
        return nm;
    }
    
    public int getStartOffset() {
        return children[0].getStartOffset();
    }
    
    public int getEndOffset() {
        Element child = (nchildren > 0) ? children[nchildren - 1] : children[0];
        return child.getEndOffset();
    }
    
    public Element getElement(int index) {
        if (index < nchildren) {
            return children[index];
        }
        return null;
    }
    
    public int getElementCount() {
        return nchildren;
    }
    
    public int getElementIndex(int offset) {
        int index;
        int lower = 0;
        int upper = nchildren - 1;
        int mid = 0;
        int p0 = getStartOffset();
        int p1;
        if (nchildren == 0) {
            return 0;
        }
        if (offset >= getEndOffset()) {
            return nchildren - 1;
        }
        if ((lastIndex >= lower) && (lastIndex <= upper)) {
            Element lastHit = children[lastIndex];
            p0 = lastHit.getStartOffset();
            p1 = lastHit.getEndOffset();
            if ((offset >= p0) && (offset < p1)) {
                return lastIndex;
            }
            if (offset < p0) {
                upper = lastIndex;
            } else {
                lower = lastIndex;
            }
        }
        while (lower <= upper) {
            mid = lower + ((upper - lower) / 2);
            Element elem = children[mid];
            p0 = elem.getStartOffset();
            p1 = elem.getEndOffset();
            if ((offset >= p0) && (offset < p1)) {
                index = mid;
                lastIndex = index;
                return index;
            } else if (offset < p0) {
                upper = mid - 1;
            } else {
                lower = mid + 1;
            }
        }
        if (offset < p0) {
            index = mid;
        } else {
            index = mid + 1;
        }
        lastIndex = index;
        return index;
    }
    
    public boolean isLeaf() {
        return false;
    }
    
    public boolean getAllowsChildren() {
        return true;
    }
    
    public Enumeration children() {
        if (nchildren == 0) return null;
        Vector tempVector = new Vector(nchildren);
        for (int counter = 0; counter < nchildren; counter++) tempVector.addElement(children[counter]);
        return tempVector.elements();
    }
    private AbstractDocument$AbstractElement[] children;
    private int nchildren;
    private int lastIndex;
}
