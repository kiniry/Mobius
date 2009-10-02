package javax.swing.tree;

import java.io.*;
import java.util.*;

final class DefaultMutableTreeNode$PostorderEnumeration implements Enumeration {
    /*synthetic*/ final DefaultMutableTreeNode this$0;
    protected TreeNode root;
    protected Enumeration children;
    protected Enumeration subtree;
    
    public DefaultMutableTreeNode$PostorderEnumeration(/*synthetic*/ final DefaultMutableTreeNode this$0, TreeNode rootNode) {
        this.this$0 = this$0;
        
        root = rootNode;
        children = root.children();
        subtree = DefaultMutableTreeNode.EMPTY_ENUMERATION;
    }
    
    public boolean hasMoreElements() {
        return root != null;
    }
    
    public TreeNode nextElement() {
        TreeNode retval;
        if (subtree.hasMoreElements()) {
            retval = (TreeNode)subtree.nextElement();
        } else if (children.hasMoreElements()) {
            subtree = new DefaultMutableTreeNode$PostorderEnumeration(this$0, (TreeNode)(TreeNode)children.nextElement());
            retval = (TreeNode)subtree.nextElement();
        } else {
            retval = root;
            root = null;
        }
        return retval;
    }
    
    /*synthetic*/ public Object nextElement() {
        return this.nextElement();
    }
}
