package javax.swing;

import java.util.Comparator;
import java.util.LinkedList;
import java.util.ListIterator;
import java.awt.Component;
import java.awt.ComponentOrientation;
import java.awt.Window;

final class LayoutComparator implements Comparator, java.io.Serializable {
    
    LayoutComparator() {
        
    }
    private static final int ROW_TOLERANCE = 10;
    private boolean horizontal = true;
    private boolean leftToRight = true;
    
    void setComponentOrientation(ComponentOrientation orientation) {
        horizontal = orientation.isHorizontal();
        leftToRight = orientation.isLeftToRight();
    }
    
    public int compare(Object o1, Object o2) {
        Component a = (Component)(Component)o1;
        Component b = (Component)(Component)o2;
        if (a == b) {
            return 0;
        }
        if (a.getParent() != b.getParent()) {
            LinkedList aAncestory;
            LinkedList bAncestory;
            for (aAncestory = new LinkedList(); a != null; a = a.getParent()) {
                aAncestory.add(a);
                if (a instanceof Window) {
                    break;
                }
            }
            if (a == null) {
                throw new ClassCastException();
            }
            for (bAncestory = new LinkedList(); b != null; b = b.getParent()) {
                bAncestory.add(b);
                if (b instanceof Window) {
                    break;
                }
            }
            if (b == null) {
                throw new ClassCastException();
            }
            for (ListIterator aIter = aAncestory.listIterator(aAncestory.size()), bIter = bAncestory.listIterator(bAncestory.size()); ; ) {
                if (aIter.hasPrevious()) {
                    a = (Component)(Component)aIter.previous();
                } else {
                    return -1;
                }
                if (bIter.hasPrevious()) {
                    b = (Component)(Component)bIter.previous();
                } else {
                    return 1;
                }
                if (a != b) {
                    break;
                }
            }
        }
        int ax = a.getX();
        int ay = a.getY();
        int bx = b.getX();
        int by = b.getY();
        int zOrder = a.getParent().getComponentZOrder(a) - b.getParent().getComponentZOrder(b);
        if (horizontal) {
            if (leftToRight) {
                if (Math.abs(ay - by) < ROW_TOLERANCE) {
                    return (ax < bx) ? -1 : ((ax > bx) ? 1 : zOrder);
                } else {
                    return (ay < by) ? -1 : 1;
                }
            } else {
                if (Math.abs(ay - by) < ROW_TOLERANCE) {
                    return (ax > bx) ? -1 : ((ax < bx) ? 1 : zOrder);
                } else {
                    return (ay < by) ? -1 : 1;
                }
            }
        } else {
            if (leftToRight) {
                if (Math.abs(ax - bx) < ROW_TOLERANCE) {
                    return (ay < by) ? -1 : ((ay > by) ? 1 : zOrder);
                } else {
                    return (ax < bx) ? -1 : 1;
                }
            } else {
                if (Math.abs(ax - bx) < ROW_TOLERANCE) {
                    return (ay < by) ? -1 : ((ay > by) ? 1 : zOrder);
                } else {
                    return (ax > bx) ? -1 : 1;
                }
            }
        }
    }
}
