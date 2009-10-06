package javax.swing.tree;

import java.io.*;
import java.util.*;

final class DefaultMutableTreeNode$PathBetweenNodesEnumeration implements Enumeration {
    /*synthetic*/ final DefaultMutableTreeNode this$0;
    protected Stack stack;
    
    public DefaultMutableTreeNode$PathBetweenNodesEnumeration(/*synthetic*/ final DefaultMutableTreeNode this$0, TreeNode ancestor, TreeNode descendant) {
        this.this$0 = this$0;
        
        if (ancestor == null || descendant == null) {
            throw new IllegalArgumentException("argument is null");
        }
        TreeNode current;
        stack = new Stack();
        stack.push(descendant);
        current = descendant;
        while (current != ancestor) {
            current = current.getParent();
            if (current == null && descendant != ancestor) {
                throw new IllegalArgumentException("node " + ancestor + " is not an ancestor of " + descendant);
            }
            stack.push(current);
        }
    }
    
    public boolean hasMoreElements() {
        return stack.size() > 0;
    }
    
    public TreeNode nextElement() {
        try {
            return (TreeNode)stack.pop();
        } catch (EmptyStackException e) {
            throw new NoSuchElementException("No more elements");
        }
    }
    
    /*synthetic public Object nextElement() {
        return this.nextElement();
    } */
}
