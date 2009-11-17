package javax.swing.text.html;

import java.util.*;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.swing.undo.*;

class HTMLDocument$LeafIterator extends HTMLDocument$Iterator {
    
    HTMLDocument$LeafIterator(HTML$Tag t, Document doc) {
        
        tag = t;
        pos = new ElementIterator(doc);
        endOffset = 0;
        next();
    }
    
    public AttributeSet getAttributes() {
        Element elem = pos.current();
        if (elem != null) {
            AttributeSet a = (AttributeSet)(AttributeSet)elem.getAttributes().getAttribute(tag);
            return a;
        }
        return null;
    }
    
    public int getStartOffset() {
        Element elem = pos.current();
        if (elem != null) {
            return elem.getStartOffset();
        }
        return -1;
    }
    
    public int getEndOffset() {
        return endOffset;
    }
    
    public void next() {
        for (nextLeaf(pos); isValid(); nextLeaf(pos)) {
            Element elem = pos.current();
            if (elem.getStartOffset() >= endOffset) {
                AttributeSet a = pos.current().getAttributes();
                if (a.isDefined(tag) || a.getAttribute(StyleConstants.NameAttribute) == tag) {
                    setEndOffset();
                    break;
                }
            }
        }
    }
    
    public HTML$Tag getTag() {
        return tag;
    }
    
    public boolean isValid() {
        return (pos.current() != null);
    }
    
    void nextLeaf(ElementIterator iter) {
        for (iter.next(); iter.current() != null; iter.next()) {
            Element e = iter.current();
            if (e.isLeaf()) {
                break;
            }
        }
    }
    
    void setEndOffset() {
        AttributeSet a0 = getAttributes();
        endOffset = pos.current().getEndOffset();
        ElementIterator fwd = (ElementIterator)(ElementIterator)pos.clone();
        for (nextLeaf(fwd); fwd.current() != null; nextLeaf(fwd)) {
            Element e = fwd.current();
            AttributeSet a1 = (AttributeSet)(AttributeSet)e.getAttributes().getAttribute(tag);
            if ((a1 == null) || (!a1.equals(a0))) {
                break;
            }
            endOffset = e.getEndOffset();
        }
    }
    private int endOffset;
    private HTML$Tag tag;
    private ElementIterator pos;
}
