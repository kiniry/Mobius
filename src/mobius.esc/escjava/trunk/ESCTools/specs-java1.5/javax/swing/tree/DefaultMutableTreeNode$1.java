package javax.swing.tree;

import java.io.*;
import java.util.*;

class DefaultMutableTreeNode$1 implements Enumeration {
    
    DefaultMutableTreeNode$1() {
        
    }
    
    public boolean hasMoreElements() {
        return false;
    }
    
    public TreeNode nextElement() {
        throw new NoSuchElementException("No more elements");
    }
    
    /*synthetic*/ public Object nextElement() {
        return this.nextElement();
    }
}
