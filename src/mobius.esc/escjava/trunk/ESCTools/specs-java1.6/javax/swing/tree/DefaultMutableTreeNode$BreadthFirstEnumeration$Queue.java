package javax.swing.tree;

import java.io.*;
import java.util.*;

final class DefaultMutableTreeNode$BreadthFirstEnumeration$Queue {
    /*synthetic*/ final DefaultMutableTreeNode$BreadthFirstEnumeration this$1;
    
    DefaultMutableTreeNode$BreadthFirstEnumeration$Queue(/*synthetic*/ final DefaultMutableTreeNode$BreadthFirstEnumeration this$1) {
        this.this$1 = this$1;
        
    }
    DefaultMutableTreeNode$BreadthFirstEnumeration$Queue$QNode head;
    DefaultMutableTreeNode$BreadthFirstEnumeration$Queue$QNode tail;
    {
    }
    
    public void enqueue(Object anObject) {
        if (head == null) {
            head = tail = new DefaultMutableTreeNode$BreadthFirstEnumeration$Queue$QNode(this, anObject, null);
        } else {
            tail.next = new DefaultMutableTreeNode$BreadthFirstEnumeration$Queue$QNode(this, anObject, null);
            tail = tail.next;
        }
    }
    
    public Object dequeue() {
        if (head == null) {
            throw new NoSuchElementException("No more elements");
        }
        Object retval = head.object;
        DefaultMutableTreeNode$BreadthFirstEnumeration$Queue$QNode oldHead = head;
        head = head.next;
        if (head == null) {
            tail = null;
        } else {
            oldHead.next = null;
        }
        return retval;
    }
    
    public Object firstObject() {
        if (head == null) {
            throw new NoSuchElementException("No more elements");
        }
        return head.object;
    }
    
    public boolean isEmpty() {
        return head == null;
    }
}
