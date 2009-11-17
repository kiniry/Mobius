package javax.swing.tree;

import java.util.Enumeration;
import java.util.NoSuchElementException;

class VariableHeightLayoutCache$VisibleTreeStateNodeEnumeration implements Enumeration {
    /*synthetic*/ final VariableHeightLayoutCache this$0;
    protected VariableHeightLayoutCache$TreeStateNode parent;
    protected int nextIndex;
    protected int childCount;
    
    protected VariableHeightLayoutCache$VisibleTreeStateNodeEnumeration(/*synthetic*/ final VariableHeightLayoutCache this$0, VariableHeightLayoutCache$TreeStateNode node) {
        this(this$0, node, -1);
    }
    
    protected VariableHeightLayoutCache$VisibleTreeStateNodeEnumeration(/*synthetic*/ final VariableHeightLayoutCache this$0, VariableHeightLayoutCache$TreeStateNode parent, int startIndex) {
        this.this$0 = this$0;
        
        this.parent = parent;
        this.nextIndex = startIndex;
        this.childCount = this.parent.getChildCount();
    }
    
    public boolean hasMoreElements() {
        return (parent != null);
    }
    
    public TreePath nextElement() {
        if (!hasMoreElements()) throw new NoSuchElementException("No more visible paths");
        TreePath retObject;
        if (nextIndex == -1) {
            retObject = parent.getTreePath();
        } else {
            VariableHeightLayoutCache$TreeStateNode node = (VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)parent.getChildAt(nextIndex);
            retObject = node.getTreePath();
        }
        updateNextObject();
        return retObject;
    }
    
    protected void updateNextObject() {
        if (!updateNextIndex()) {
            findNextValidParent();
        }
    }
    
    protected boolean findNextValidParent() {
        if (parent == VariableHeightLayoutCache.access$200(this$0)) {
            parent = null;
            return false;
        }
        while (parent != null) {
            VariableHeightLayoutCache$TreeStateNode newParent = (VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)parent.getParent();
            if (newParent != null) {
                nextIndex = newParent.getIndex(parent);
                parent = newParent;
                childCount = parent.getChildCount();
                if (updateNextIndex()) return true;
            } else parent = null;
        }
        return false;
    }
    
    protected boolean updateNextIndex() {
        if (nextIndex == -1 && !parent.isExpanded()) return false;
        if (childCount == 0) return false; else if (++nextIndex >= childCount) return false;
        VariableHeightLayoutCache$TreeStateNode child = (VariableHeightLayoutCache$TreeStateNode)(VariableHeightLayoutCache$TreeStateNode)parent.getChildAt(nextIndex);
        if (child != null && child.isExpanded()) {
            parent = child;
            nextIndex = -1;
            childCount = child.getChildCount();
        }
        return true;
    }
    
    /*synthetic public Object nextElement() {
        return this.nextElement();
    } */
}
