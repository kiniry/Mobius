package javax.swing.tree;

import java.util.Enumeration;
import java.util.NoSuchElementException;

class FixedHeightLayoutCache$VisibleFHTreeStateNodeEnumeration implements Enumeration {
    /*synthetic*/ final FixedHeightLayoutCache this$0;
    protected FixedHeightLayoutCache$FHTreeStateNode parent;
    protected int nextIndex;
    protected int childCount;
    
    protected FixedHeightLayoutCache$VisibleFHTreeStateNodeEnumeration(/*synthetic*/ final FixedHeightLayoutCache this$0, FixedHeightLayoutCache$FHTreeStateNode node) {
        this(this$0, node, -1);
    }
    
    protected FixedHeightLayoutCache$VisibleFHTreeStateNodeEnumeration(/*synthetic*/ final FixedHeightLayoutCache this$0, FixedHeightLayoutCache$FHTreeStateNode parent, int startIndex) {
        this.this$0 = this$0;
        
        this.parent = parent;
        this.nextIndex = startIndex;
        this.childCount = this$0.treeModel.getChildCount(this.parent.getUserObject());
    }
    
    public boolean hasMoreElements() {
        return (parent != null);
    }
    
    public TreePath nextElement() {
        if (!hasMoreElements()) throw new NoSuchElementException("No more visible paths");
        TreePath retObject;
        if (nextIndex == -1) retObject = parent.getTreePath(); else {
            FixedHeightLayoutCache$FHTreeStateNode node = parent.getChildAtModelIndex(nextIndex);
            if (node == null) retObject = parent.getTreePath().pathByAddingChild(this$0.treeModel.getChild(parent.getUserObject(), nextIndex)); else retObject = node.getTreePath();
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
        if (parent == FixedHeightLayoutCache.access$600(this$0)) {
            parent = null;
            return false;
        }
        while (parent != null) {
            FixedHeightLayoutCache$FHTreeStateNode newParent = (FixedHeightLayoutCache$FHTreeStateNode)(FixedHeightLayoutCache$FHTreeStateNode)parent.getParent();
            if (newParent != null) {
                nextIndex = parent.childIndex;
                parent = newParent;
                childCount = this$0.treeModel.getChildCount(parent.getUserObject());
                if (updateNextIndex()) return true;
            } else parent = null;
        }
        return false;
    }
    
    protected boolean updateNextIndex() {
        if (nextIndex == -1 && !parent.isExpanded()) {
            return false;
        }
        if (childCount == 0) {
            return false;
        } else if (++nextIndex >= childCount) {
            return false;
        }
        FixedHeightLayoutCache$FHTreeStateNode child = parent.getChildAtModelIndex(nextIndex);
        if (child != null && child.isExpanded()) {
            parent = child;
            nextIndex = -1;
            childCount = this$0.treeModel.getChildCount(child.getUserObject());
        }
        return true;
    }
    
    /*synthetic public Object nextElement() {
        return this.nextElement();
    } */
}
