package javax.swing.tree;

import java.io.*;
import java.util.*;

final class DefaultMutableTreeNode$PreorderEnumeration implements Enumeration {
    /*synthetic*/ final DefaultMutableTreeNode this$0;
    protected Stack stack;
    
    public DefaultMutableTreeNode$PreorderEnumeration(/*synthetic*/ final DefaultMutableTreeNode this$0, TreeNode rootNode) {
        this.this$0 = this$0;
        
        Vector v = new Vector(1);
        v.addElement(rootNode);
        stack = new Stack();
        stack.push(v.elements());
    }
    
    public boolean hasMoreElements() {
        return (!stack.empty() && ((Enumeration)(Enumeration)stack.peek()).hasMoreElements());
    }
    
    public TreeNode nextElement() {
        Enumeration enumer = (Enumeration)(Enumeration)stack.peek();
        TreeNode node = (TreeNode)(TreeNode)enumer.nextElement();
        Enumeration children = node.children();
        if (!enumer.hasMoreElements()) {
            stack.pop();
        }
        if (children.hasMoreElements()) {
            stack.push(children);
        }
        return node;
    }
    
    /*synthetic public Object nextElement() {
        return this.nextElement();
    } */
}
