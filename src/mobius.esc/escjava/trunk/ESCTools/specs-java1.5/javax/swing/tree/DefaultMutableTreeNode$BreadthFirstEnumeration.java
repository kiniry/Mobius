package javax.swing.tree;

import java.io.*;
import java.util.*;

final class DefaultMutableTreeNode$BreadthFirstEnumeration implements Enumeration {
    /*synthetic*/ final DefaultMutableTreeNode this$0;
    protected DefaultMutableTreeNode$BreadthFirstEnumeration$Queue queue;
    
    public DefaultMutableTreeNode$BreadthFirstEnumeration(/*synthetic*/ final DefaultMutableTreeNode this$0, TreeNode rootNode) {
        this.this$0 = this$0;
        
        Vector v = new Vector(1);
        v.addElement(rootNode);
        queue = new DefaultMutableTreeNode$BreadthFirstEnumeration$Queue(this);
        queue.enqueue(v.elements());
    }
    
    public boolean hasMoreElements() {
        return (!queue.isEmpty() && ((Enumeration)(Enumeration)queue.firstObject()).hasMoreElements());
    }
    
    public TreeNode nextElement() {
        Enumeration enumer = (Enumeration)(Enumeration)queue.firstObject();
        TreeNode node = (TreeNode)(TreeNode)enumer.nextElement();
        Enumeration children = node.children();
        if (!enumer.hasMoreElements()) {
            queue.dequeue();
        }
        if (children.hasMoreElements()) {
            queue.enqueue(children);
        }
        return node;
    }
    {
    }
    
    /*synthetic*/ public Object nextElement() {
        return this.nextElement();
    }
}
