package javax.swing.text;

import java.awt.*;
import javax.swing.SwingConstants;
import javax.swing.event.*;

public abstract class View implements SwingConstants {
    
    public View(Element elem) {
        
        this.elem = elem;
    }
    
    public View getParent() {
        return parent;
    }
    
    public boolean isVisible() {
        return true;
    }
    
    public abstract float getPreferredSpan(int axis);
    
    public float getMinimumSpan(int axis) {
        int w = getResizeWeight(axis);
        if (w == 0) {
            return getPreferredSpan(axis);
        }
        return 0;
    }
    
    public float getMaximumSpan(int axis) {
        int w = getResizeWeight(axis);
        if (w == 0) {
            return getPreferredSpan(axis);
        }
        return Integer.MAX_VALUE;
    }
    
    public void preferenceChanged(View child, boolean width, boolean height) {
        View parent = getParent();
        if (parent != null) {
            parent.preferenceChanged(this, width, height);
        }
    }
    
    public float getAlignment(int axis) {
        return 0.5F;
    }
    
    public abstract void paint(Graphics g, Shape allocation);
    
    public void setParent(View parent) {
        if (parent == null) {
            for (int i = 0; i < getViewCount(); i++) {
                if (getView(i).getParent() == this) {
                    getView(i).setParent(null);
                }
            }
        }
        this.parent = parent;
    }
    
    public int getViewCount() {
        return 0;
    }
    
    public View getView(int n) {
        return null;
    }
    
    public void removeAll() {
        replace(0, getViewCount(), null);
    }
    
    public void remove(int i) {
        replace(i, 1, null);
    }
    
    public void insert(int offs, View v) {
        View[] one = new View[1];
        one[0] = v;
        replace(offs, 0, one);
    }
    
    public void append(View v) {
        View[] one = new View[1];
        one[0] = v;
        replace(getViewCount(), 0, one);
    }
    
    public void replace(int offset, int length, View[] views) {
    }
    
    public int getViewIndex(int pos, Position$Bias b) {
        return -1;
    }
    
    public Shape getChildAllocation(int index, Shape a) {
        return null;
    }
    
    public int getNextVisualPositionFrom(int pos, Position$Bias b, Shape a, int direction, Position$Bias[] biasRet) throws BadLocationException {
        biasRet[0] = Position$Bias.Forward;
        switch (direction) {
        case NORTH: 
        
        case SOUTH: 
            {
                if (pos == -1) {
                    pos = (direction == NORTH) ? Math.max(0, getEndOffset() - 1) : getStartOffset();
                    break;
                }
                JTextComponent target = (JTextComponent)(JTextComponent)getContainer();
                Caret c = (target != null) ? target.getCaret() : null;
                Point mcp;
                if (c != null) {
                    mcp = c.getMagicCaretPosition();
                } else {
                    mcp = null;
                }
                int x;
                if (mcp == null) {
                    Rectangle loc = target.modelToView(pos);
                    x = (loc == null) ? 0 : loc.x;
                } else {
                    x = mcp.x;
                }
                if (direction == NORTH) {
                    pos = Utilities.getPositionAbove(target, pos, x);
                } else {
                    pos = Utilities.getPositionBelow(target, pos, x);
                }
            }
            break;
        
        case WEST: 
            if (pos == -1) {
                pos = Math.max(0, getEndOffset() - 1);
            } else {
                pos = Math.max(0, pos - 1);
            }
            break;
        
        case EAST: 
            if (pos == -1) {
                pos = getStartOffset();
            } else {
                pos = Math.min(pos + 1, getDocument().getLength());
            }
            break;
        
        default: 
            throw new IllegalArgumentException("Bad direction: " + direction);
        
        }
        return pos;
    }
    
    public abstract Shape modelToView(int pos, Shape a, Position$Bias b) throws BadLocationException;
    
    public Shape modelToView(int p0, Position$Bias b0, int p1, Position$Bias b1, Shape a) throws BadLocationException {
        Shape s0 = modelToView(p0, a, b0);
        Shape s1;
        if (p1 == getEndOffset()) {
            try {
                s1 = modelToView(p1, a, b1);
            } catch (BadLocationException ble) {
                s1 = null;
            }
            if (s1 == null) {
                Rectangle alloc = (a instanceof Rectangle) ? (Rectangle)(Rectangle)a : a.getBounds();
                s1 = new Rectangle(alloc.x + alloc.width - 1, alloc.y, 1, alloc.height);
            }
        } else {
            s1 = modelToView(p1, a, b1);
        }
        Rectangle r0 = s0.getBounds();
        Rectangle r1 = (s1 instanceof Rectangle) ? (Rectangle)(Rectangle)s1 : s1.getBounds();
        if (r0.y != r1.y) {
            Rectangle alloc = (a instanceof Rectangle) ? (Rectangle)(Rectangle)a : a.getBounds();
            r0.x = alloc.x;
            r0.width = alloc.width;
        }
        r0.add(r1);
        return r0;
    }
    
    public abstract int viewToModel(float x, float y, Shape a, Position$Bias[] biasReturn);
    
    public void insertUpdate(DocumentEvent e, Shape a, ViewFactory f) {
        if (getViewCount() > 0) {
            Element elem = getElement();
            DocumentEvent$ElementChange ec = e.getChange(elem);
            if (ec != null) {
                if (!updateChildren(ec, e, f)) {
                    ec = null;
                }
            }
            forwardUpdate(ec, e, a, f);
            updateLayout(ec, e, a);
        }
    }
    
    public void removeUpdate(DocumentEvent e, Shape a, ViewFactory f) {
        if (getViewCount() > 0) {
            Element elem = getElement();
            DocumentEvent$ElementChange ec = e.getChange(elem);
            if (ec != null) {
                if (!updateChildren(ec, e, f)) {
                    ec = null;
                }
            }
            forwardUpdate(ec, e, a, f);
            updateLayout(ec, e, a);
        }
    }
    
    public void changedUpdate(DocumentEvent e, Shape a, ViewFactory f) {
        if (getViewCount() > 0) {
            Element elem = getElement();
            DocumentEvent$ElementChange ec = e.getChange(elem);
            if (ec != null) {
                if (!updateChildren(ec, e, f)) {
                    ec = null;
                }
            }
            forwardUpdate(ec, e, a, f);
            updateLayout(ec, e, a);
        }
    }
    
    public Document getDocument() {
        return elem.getDocument();
    }
    
    public int getStartOffset() {
        return elem.getStartOffset();
    }
    
    public int getEndOffset() {
        return elem.getEndOffset();
    }
    
    public Element getElement() {
        return elem;
    }
    
    public Graphics getGraphics() {
        Component c = getContainer();
        return c.getGraphics();
    }
    
    public AttributeSet getAttributes() {
        return elem.getAttributes();
    }
    
    public View breakView(int axis, int offset, float pos, float len) {
        return this;
    }
    
    public View createFragment(int p0, int p1) {
        return this;
    }
    
    public int getBreakWeight(int axis, float pos, float len) {
        if (len > getPreferredSpan(axis)) {
            return GoodBreakWeight;
        }
        return BadBreakWeight;
    }
    
    public int getResizeWeight(int axis) {
        return 0;
    }
    
    public void setSize(float width, float height) {
    }
    
    public Container getContainer() {
        View v = getParent();
        return (v != null) ? v.getContainer() : null;
    }
    
    public ViewFactory getViewFactory() {
        View v = getParent();
        return (v != null) ? v.getViewFactory() : null;
    }
    
    public String getToolTipText(float x, float y, Shape allocation) {
        int viewIndex = getViewIndex(x, y, allocation);
        if (viewIndex >= 0) {
            allocation = getChildAllocation(viewIndex, allocation);
            Rectangle rect = (allocation instanceof Rectangle) ? (Rectangle)(Rectangle)allocation : allocation.getBounds();
            if (rect.contains(x, y)) {
                return getView(viewIndex).getToolTipText(x, y, allocation);
            }
        }
        return null;
    }
    
    public int getViewIndex(float x, float y, Shape allocation) {
        for (int counter = getViewCount() - 1; counter >= 0; counter--) {
            Shape childAllocation = getChildAllocation(counter, allocation);
            if (childAllocation != null) {
                Rectangle rect = (childAllocation instanceof Rectangle) ? (Rectangle)(Rectangle)childAllocation : allocation.getBounds();
                if (rect.contains(x, y)) {
                    return counter;
                }
            }
        }
        return -1;
    }
    
    protected boolean updateChildren(DocumentEvent$ElementChange ec, DocumentEvent e, ViewFactory f) {
        Element[] removedElems = ec.getChildrenRemoved();
        Element[] addedElems = ec.getChildrenAdded();
        View[] added = null;
        if (addedElems != null) {
            added = new View[addedElems.length];
            for (int i = 0; i < addedElems.length; i++) {
                added[i] = f.create(addedElems[i]);
            }
        }
        int nremoved = 0;
        int index = ec.getIndex();
        if (removedElems != null) {
            nremoved = removedElems.length;
        }
        replace(index, nremoved, added);
        return true;
    }
    
    protected void forwardUpdate(DocumentEvent$ElementChange ec, DocumentEvent e, Shape a, ViewFactory f) {
        Element elem = getElement();
        int pos = e.getOffset();
        int index0 = getViewIndex(pos, Position$Bias.Forward);
        if (index0 == -1 && e.getType() == DocumentEvent$EventType.REMOVE && pos >= getEndOffset()) {
            index0 = getViewCount() - 1;
        }
        int index1 = index0;
        View v = (index0 >= 0) ? getView(index0) : null;
        if (v != null) {
            if ((v.getStartOffset() == pos) && (pos > 0)) {
                index0 = Math.max(index0 - 1, 0);
            }
        }
        if (e.getType() != DocumentEvent$EventType.REMOVE) {
            index1 = getViewIndex(pos + e.getLength(), Position$Bias.Forward);
            if (index1 < 0) {
                index1 = getViewCount() - 1;
            }
        }
        int hole0 = index1 + 1;
        int hole1 = hole0;
        Element[] addedElems = (ec != null) ? ec.getChildrenAdded() : null;
        if ((addedElems != null) && (addedElems.length > 0)) {
            hole0 = ec.getIndex();
            hole1 = hole0 + addedElems.length - 1;
        }
        index0 = Math.max(index0, 0);
        for (int i = index0; i <= index1; i++) {
            if (!((i >= hole0) && (i <= hole1))) {
                v = getView(i);
                if (v != null) {
                    Shape childAlloc = getChildAllocation(i, a);
                    forwardUpdateToView(v, e, childAlloc, f);
                }
            }
        }
    }
    
    protected void forwardUpdateToView(View v, DocumentEvent e, Shape a, ViewFactory f) {
        DocumentEvent$EventType type = e.getType();
        if (type == DocumentEvent$EventType.INSERT) {
            v.insertUpdate(e, a, f);
        } else if (type == DocumentEvent$EventType.REMOVE) {
            v.removeUpdate(e, a, f);
        } else {
            v.changedUpdate(e, a, f);
        }
    }
    
    protected void updateLayout(DocumentEvent$ElementChange ec, DocumentEvent e, Shape a) {
        if ((ec != null) && (a != null)) {
            preferenceChanged(null, true, true);
            Container host = getContainer();
            if (host != null) {
                host.repaint();
            }
        }
    }
    public static final int BadBreakWeight = 0;
    public static final int GoodBreakWeight = 1000;
    public static final int ExcellentBreakWeight = 2000;
    public static final int ForcedBreakWeight = 3000;
    public static final int X_AXIS = HORIZONTAL;
    public static final int Y_AXIS = VERTICAL;
    
    
    public Shape modelToView(int pos, Shape a) throws BadLocationException {
        return modelToView(pos, a, Position$Bias.Forward);
    }
    
    
    public int viewToModel(float x, float y, Shape a) {
        sharedBiasReturn[0] = Position$Bias.Forward;
        return viewToModel(x, y, a, sharedBiasReturn);
    }
    static final Position$Bias[] sharedBiasReturn = new Position$Bias[1];
    private View parent;
    private Element elem;
}
