package javax.swing.text;

import java.awt.*;
import javax.swing.event.*;

public abstract class CompositeView extends View {
    
    public CompositeView(Element elem) {
        super(elem);
        children = new View[1];
        nchildren = 0;
        childAlloc = new Rectangle();
    }
    
    protected void loadChildren(ViewFactory f) {
        if (f == null) {
            return;
        }
        Element e = getElement();
        int n = e.getElementCount();
        if (n > 0) {
            View[] added = new View[n];
            for (int i = 0; i < n; i++) {
                added[i] = f.create(e.getElement(i));
            }
            replace(0, 0, added);
        }
    }
    
    public void setParent(View parent) {
        super.setParent(parent);
        if ((parent != null) && (nchildren == 0)) {
            ViewFactory f = getViewFactory();
            loadChildren(f);
        }
    }
    
    public int getViewCount() {
        return nchildren;
    }
    
    public View getView(int n) {
        return children[n];
    }
    
    public void replace(int offset, int length, View[] views) {
        if (views == null) {
            views = ZERO;
        }
        for (int i = offset; i < offset + length; i++) {
            if (children[i].getParent() == this) {
                children[i].setParent(null);
            }
            children[i] = null;
        }
        int delta = views.length - length;
        int src = offset + length;
        int nmove = nchildren - src;
        int dest = src + delta;
        if ((nchildren + delta) >= children.length) {
            int newLength = Math.max(2 * children.length, nchildren + delta);
            View[] newChildren = new View[newLength];
            System.arraycopy(children, 0, newChildren, 0, offset);
            System.arraycopy(views, 0, newChildren, offset, views.length);
            System.arraycopy(children, src, newChildren, dest, nmove);
            children = newChildren;
        } else {
            System.arraycopy(children, src, children, dest, nmove);
            System.arraycopy(views, 0, children, offset, views.length);
        }
        nchildren = nchildren + delta;
        for (int i = 0; i < views.length; i++) {
            views[i].setParent(this);
        }
    }
    
    public Shape getChildAllocation(int index, Shape a) {
        Rectangle alloc = getInsideAllocation(a);
        childAllocation(index, alloc);
        return alloc;
    }
    
    public Shape modelToView(int pos, Shape a, Position$Bias b) throws BadLocationException {
        boolean isBackward = (b == Position$Bias.Backward);
        int testPos = (isBackward) ? Math.max(0, pos - 1) : pos;
        if (isBackward && testPos < getStartOffset()) {
            return null;
        }
        int vIndex = getViewIndexAtPosition(testPos);
        if ((vIndex != -1) && (vIndex < getViewCount())) {
            View v = getView(vIndex);
            if (v != null && testPos >= v.getStartOffset() && testPos < v.getEndOffset()) {
                Shape childShape = getChildAllocation(vIndex, a);
                if (childShape == null) {
                    return null;
                }
                Shape retShape = v.modelToView(pos, childShape, b);
                if (retShape == null && v.getEndOffset() == pos) {
                    if (++vIndex < getViewCount()) {
                        v = getView(vIndex);
                        retShape = v.modelToView(pos, getChildAllocation(vIndex, a), b);
                    }
                }
                return retShape;
            }
        }
        throw new BadLocationException("Position not represented by view", pos);
    }
    
    public Shape modelToView(int p0, Position$Bias b0, int p1, Position$Bias b1, Shape a) throws BadLocationException {
        if (p0 == getStartOffset() && p1 == getEndOffset()) {
            return a;
        }
        Rectangle alloc = getInsideAllocation(a);
        Rectangle r0 = new Rectangle(alloc);
        View v0 = getViewAtPosition((b0 == Position$Bias.Backward) ? Math.max(0, p0 - 1) : p0, r0);
        Rectangle r1 = new Rectangle(alloc);
        View v1 = getViewAtPosition((b1 == Position$Bias.Backward) ? Math.max(0, p1 - 1) : p1, r1);
        if (v0 == v1) {
            if (v0 == null) {
                return a;
            }
            return v0.modelToView(p0, b0, p1, b1, r0);
        }
        int viewCount = getViewCount();
        int counter = 0;
        while (counter < viewCount) {
            View v;
            if ((v = getView(counter)) == v0 || v == v1) {
                View endView;
                Rectangle retRect;
                Rectangle tempRect = new Rectangle();
                if (v == v0) {
                    retRect = v0.modelToView(p0, b0, v0.getEndOffset(), Position$Bias.Backward, r0).getBounds();
                    endView = v1;
                } else {
                    retRect = v1.modelToView(v1.getStartOffset(), Position$Bias.Forward, p1, b1, r1).getBounds();
                    endView = v0;
                }
                while (++counter < viewCount && (v = getView(counter)) != endView) {
                    tempRect.setBounds(alloc);
                    childAllocation(counter, tempRect);
                    retRect.add(tempRect);
                }
                if (endView != null) {
                    Shape endShape;
                    if (endView == v1) {
                        endShape = v1.modelToView(v1.getStartOffset(), Position$Bias.Forward, p1, b1, r1);
                    } else {
                        endShape = v0.modelToView(p0, b0, v0.getEndOffset(), Position$Bias.Backward, r0);
                    }
                    if (endShape instanceof Rectangle) {
                        retRect.add((Rectangle)(Rectangle)endShape);
                    } else {
                        retRect.add(endShape.getBounds());
                    }
                }
                return retRect;
            }
            counter++;
        }
        throw new BadLocationException("Position not represented by view", p0);
    }
    
    public int viewToModel(float x, float y, Shape a, Position$Bias[] bias) {
        Rectangle alloc = getInsideAllocation(a);
        if (isBefore((int)x, (int)y, alloc)) {
            int retValue = -1;
            try {
                retValue = getNextVisualPositionFrom(-1, Position$Bias.Forward, a, EAST, bias);
            } catch (BadLocationException ble) {
            } catch (IllegalArgumentException iae) {
            }
            if (retValue == -1) {
                retValue = getStartOffset();
                bias[0] = Position$Bias.Forward;
            }
            return retValue;
        } else if (isAfter((int)x, (int)y, alloc)) {
            int retValue = -1;
            try {
                retValue = getNextVisualPositionFrom(-1, Position$Bias.Forward, a, WEST, bias);
            } catch (BadLocationException ble) {
            } catch (IllegalArgumentException iae) {
            }
            if (retValue == -1) {
                retValue = getEndOffset() - 1;
                bias[0] = Position$Bias.Forward;
            }
            return retValue;
        } else {
            View v = getViewAtPoint((int)x, (int)y, alloc);
            if (v != null) {
                return v.viewToModel(x, y, alloc, bias);
            }
        }
        return -1;
    }
    
    public int getNextVisualPositionFrom(int pos, Position$Bias b, Shape a, int direction, Position$Bias[] biasRet) throws BadLocationException {
        Rectangle alloc = getInsideAllocation(a);
        switch (direction) {
        case NORTH: 
            return getNextNorthSouthVisualPositionFrom(pos, b, a, direction, biasRet);
        
        case SOUTH: 
            return getNextNorthSouthVisualPositionFrom(pos, b, a, direction, biasRet);
        
        case EAST: 
            return getNextEastWestVisualPositionFrom(pos, b, a, direction, biasRet);
        
        case WEST: 
            return getNextEastWestVisualPositionFrom(pos, b, a, direction, biasRet);
        
        default: 
            throw new IllegalArgumentException("Bad direction: " + direction);
        
        }
    }
    
    public int getViewIndex(int pos, Position$Bias b) {
        if (b == Position$Bias.Backward) {
            pos -= 1;
        }
        if ((pos >= getStartOffset()) && (pos < getEndOffset())) {
            return getViewIndexAtPosition(pos);
        }
        return -1;
    }
    
    protected abstract boolean isBefore(int x, int y, Rectangle alloc);
    
    protected abstract boolean isAfter(int x, int y, Rectangle alloc);
    
    protected abstract View getViewAtPoint(int x, int y, Rectangle alloc);
    
    protected abstract void childAllocation(int index, Rectangle a);
    
    protected View getViewAtPosition(int pos, Rectangle a) {
        int index = getViewIndexAtPosition(pos);
        if ((index >= 0) && (index < getViewCount())) {
            View v = getView(index);
            if (a != null) {
                childAllocation(index, a);
            }
            return v;
        }
        return null;
    }
    
    protected int getViewIndexAtPosition(int pos) {
        Element elem = getElement();
        return elem.getElementIndex(pos);
    }
    
    protected Rectangle getInsideAllocation(Shape a) {
        if (a != null) {
            Rectangle alloc;
            if (a instanceof Rectangle) {
                alloc = (Rectangle)(Rectangle)a;
            } else {
                alloc = a.getBounds();
            }
            childAlloc.setBounds(alloc);
            childAlloc.x += getLeftInset();
            childAlloc.y += getTopInset();
            childAlloc.width -= getLeftInset() + getRightInset();
            childAlloc.height -= getTopInset() + getBottomInset();
            return childAlloc;
        }
        return null;
    }
    
    protected void setParagraphInsets(AttributeSet attr) {
        top = (short)StyleConstants.getSpaceAbove(attr);
        left = (short)StyleConstants.getLeftIndent(attr);
        bottom = (short)StyleConstants.getSpaceBelow(attr);
        right = (short)StyleConstants.getRightIndent(attr);
    }
    
    protected void setInsets(short top, short left, short bottom, short right) {
        this.top = top;
        this.left = left;
        this.right = right;
        this.bottom = bottom;
    }
    
    protected short getLeftInset() {
        return left;
    }
    
    protected short getRightInset() {
        return right;
    }
    
    protected short getTopInset() {
        return top;
    }
    
    protected short getBottomInset() {
        return bottom;
    }
    
    protected int getNextNorthSouthVisualPositionFrom(int pos, Position$Bias b, Shape a, int direction, Position$Bias[] biasRet) throws BadLocationException {
        return Utilities.getNextVisualPositionFrom(this, pos, b, a, direction, biasRet);
    }
    
    protected int getNextEastWestVisualPositionFrom(int pos, Position$Bias b, Shape a, int direction, Position$Bias[] biasRet) throws BadLocationException {
        return Utilities.getNextVisualPositionFrom(this, pos, b, a, direction, biasRet);
    }
    
    protected boolean flipEastAndWestAtEnds(int position, Position$Bias bias) {
        return false;
    }
    private static View[] ZERO = new View[0];
    private View[] children;
    private int nchildren;
    private short left;
    private short right;
    private short top;
    private short bottom;
    private Rectangle childAlloc;
}
