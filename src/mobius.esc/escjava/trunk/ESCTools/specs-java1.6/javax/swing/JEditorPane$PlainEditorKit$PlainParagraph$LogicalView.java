package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.net.*;
import java.util.*;
import java.io.*;
import java.util.*;
import javax.swing.plaf.*;
import javax.swing.text.*;
import javax.swing.event.*;
import javax.swing.text.html.*;
import javax.accessibility.*;

class JEditorPane$PlainEditorKit$PlainParagraph$LogicalView extends CompositeView {
    
    JEditorPane$PlainEditorKit$PlainParagraph$LogicalView(Element elem) {
        super(elem);
    }
    
    protected int getViewIndexAtPosition(int pos) {
        Element elem = getElement();
        if (elem.getElementCount() > 0) {
            return elem.getElementIndex(pos);
        }
        return 0;
    }
    
    protected boolean updateChildren(DocumentEvent$ElementChange ec, DocumentEvent e, ViewFactory f) {
        return false;
    }
    
    protected void loadChildren(ViewFactory f) {
        Element elem = getElement();
        if (elem.getElementCount() > 0) {
            super.loadChildren(f);
        } else {
            View v = new GlyphView(elem);
            append(v);
        }
    }
    
    public float getPreferredSpan(int axis) {
        if (getViewCount() != 1) throw new Error("One child view is assumed.");
        View v = getView(0);
        return v.getPreferredSpan(axis);
    }
    
    protected void forwardUpdateToView(View v, DocumentEvent e, Shape a, ViewFactory f) {
        v.setParent(this);
        super.forwardUpdateToView(v, e, a, f);
    }
    
    public void paint(Graphics g, Shape allocation) {
    }
    
    protected boolean isBefore(int x, int y, Rectangle alloc) {
        return false;
    }
    
    protected boolean isAfter(int x, int y, Rectangle alloc) {
        return false;
    }
    
    protected View getViewAtPoint(int x, int y, Rectangle alloc) {
        return null;
    }
    
    protected void childAllocation(int index, Rectangle a) {
    }
}
