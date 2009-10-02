package javax.swing.tree;

import java.io.*;
import java.util.*;

public class DefaultMutableTreeNode extends Object implements Cloneable, MutableTreeNode, Serializable {
    public static final Enumeration EMPTY_ENUMERATION = new DefaultMutableTreeNode$1();
    protected MutableTreeNode parent;
    protected Vector children;
    protected transient Object userObject;
    protected boolean allowsChildren;
    
    public DefaultMutableTreeNode() {
        this(null);
    }
    
    public DefaultMutableTreeNode(Object userObject) {
        this(userObject, true);
    }
    
    public DefaultMutableTreeNode(Object userObject, boolean allowsChildren) {
        
        parent = null;
        this.allowsChildren = allowsChildren;
        this.userObject = userObject;
    }
    
    public void insert(MutableTreeNode newChild, int childIndex) {
        if (!allowsChildren) {
            throw new IllegalStateException("node does not allow children");
        } else if (newChild == null) {
            throw new IllegalArgumentException("new child is null");
        } else if (isNodeAncestor(newChild)) {
            throw new IllegalArgumentException("new child is an ancestor");
        }
        MutableTreeNode oldParent = (MutableTreeNode)(MutableTreeNode)newChild.getParent();
        if (oldParent != null) {
            oldParent.remove(newChild);
        }
        newChild.setParent(this);
        if (children == null) {
            children = new Vector();
        }
        children.insertElementAt(newChild, childIndex);
    }
    
    public void remove(int childIndex) {
        MutableTreeNode child = (MutableTreeNode)(MutableTreeNode)getChildAt(childIndex);
        children.removeElementAt(childIndex);
        child.setParent(null);
    }
    
    public void setParent(MutableTreeNode newParent) {
        parent = newParent;
    }
    
    public TreeNode getParent() {
        return parent;
    }
    
    public TreeNode getChildAt(int index) {
        if (children == null) {
            throw new ArrayIndexOutOfBoundsException("node has no children");
        }
        return (TreeNode)(TreeNode)children.elementAt(index);
    }
    
    public int getChildCount() {
        if (children == null) {
            return 0;
        } else {
            return children.size();
        }
    }
    
    public int getIndex(TreeNode aChild) {
        if (aChild == null) {
            throw new IllegalArgumentException("argument is null");
        }
        if (!isNodeChild(aChild)) {
            return -1;
        }
        return children.indexOf(aChild);
    }
    
    public Enumeration children() {
        if (children == null) {
            return EMPTY_ENUMERATION;
        } else {
            return children.elements();
        }
    }
    
    public void setAllowsChildren(boolean allows) {
        if (allows != allowsChildren) {
            allowsChildren = allows;
            if (!allowsChildren) {
                removeAllChildren();
            }
        }
    }
    
    public boolean getAllowsChildren() {
        return allowsChildren;
    }
    
    public void setUserObject(Object userObject) {
        this.userObject = userObject;
    }
    
    public Object getUserObject() {
        return userObject;
    }
    
    public void removeFromParent() {
        MutableTreeNode parent = (MutableTreeNode)(MutableTreeNode)getParent();
        if (parent != null) {
            parent.remove(this);
        }
    }
    
    public void remove(MutableTreeNode aChild) {
        if (aChild == null) {
            throw new IllegalArgumentException("argument is null");
        }
        if (!isNodeChild(aChild)) {
            throw new IllegalArgumentException("argument is not a child");
        }
        remove(getIndex(aChild));
    }
    
    public void removeAllChildren() {
        for (int i = getChildCount() - 1; i >= 0; i--) {
            remove(i);
        }
    }
    
    public void add(MutableTreeNode newChild) {
        if (newChild != null && newChild.getParent() == this) insert(newChild, getChildCount() - 1); else insert(newChild, getChildCount());
    }
    
    public boolean isNodeAncestor(TreeNode anotherNode) {
        if (anotherNode == null) {
            return false;
        }
        TreeNode ancestor = this;
        do {
            if (ancestor == anotherNode) {
                return true;
            }
        }         while ((ancestor = ancestor.getParent()) != null);
        return false;
    }
    
    public boolean isNodeDescendant(DefaultMutableTreeNode anotherNode) {
        if (anotherNode == null) return false;
        return anotherNode.isNodeAncestor(this);
    }
    
    public TreeNode getSharedAncestor(DefaultMutableTreeNode aNode) {
        if (aNode == this) {
            return this;
        } else if (aNode == null) {
            return null;
        }
        int level1;
        int level2;
        int diff;
        TreeNode node1;
        TreeNode node2;
        level1 = getLevel();
        level2 = aNode.getLevel();
        if (level2 > level1) {
            diff = level2 - level1;
            node1 = aNode;
            node2 = this;
        } else {
            diff = level1 - level2;
            node1 = this;
            node2 = aNode;
        }
        while (diff > 0) {
            node1 = node1.getParent();
            diff--;
        }
        do {
            if (node1 == node2) {
                return node1;
            }
            node1 = node1.getParent();
            node2 = node2.getParent();
        }         while (node1 != null);
        if (node1 != null || node2 != null) {
            throw new Error("nodes should be null");
        }
        return null;
    }
    
    public boolean isNodeRelated(DefaultMutableTreeNode aNode) {
        return (aNode != null) && (getRoot() == aNode.getRoot());
    }
    
    public int getDepth() {
        Object last = null;
        Enumeration enum_ = breadthFirstEnumeration();
        while (enum_.hasMoreElements()) {
            last = enum_.nextElement();
        }
        if (last == null) {
            throw new Error("nodes should be null");
        }
        return ((DefaultMutableTreeNode)(DefaultMutableTreeNode)last).getLevel() - getLevel();
    }
    
    public int getLevel() {
        TreeNode ancestor;
        int levels = 0;
        ancestor = this;
        while ((ancestor = ancestor.getParent()) != null) {
            levels++;
        }
        return levels;
    }
    
    public TreeNode[] getPath() {
        return getPathToRoot(this, 0);
    }
    
    protected TreeNode[] getPathToRoot(TreeNode aNode, int depth) {
        TreeNode[] retNodes;
        if (aNode == null) {
            if (depth == 0) return null; else retNodes = new TreeNode[depth];
        } else {
            depth++;
            retNodes = getPathToRoot(aNode.getParent(), depth);
            retNodes[retNodes.length - depth] = aNode;
        }
        return retNodes;
    }
    
    public Object[] getUserObjectPath() {
        TreeNode[] realPath = getPath();
        Object[] retPath = new Object[realPath.length];
        for (int counter = 0; counter < realPath.length; counter++) retPath[counter] = ((DefaultMutableTreeNode)(DefaultMutableTreeNode)realPath[counter]).getUserObject();
        return retPath;
    }
    
    public TreeNode getRoot() {
        TreeNode ancestor = this;
        TreeNode previous;
        do {
            previous = ancestor;
            ancestor = ancestor.getParent();
        }         while (ancestor != null);
        return previous;
    }
    
    public boolean isRoot() {
        return getParent() == null;
    }
    
    public DefaultMutableTreeNode getNextNode() {
        if (getChildCount() == 0) {
            DefaultMutableTreeNode nextSibling = getNextSibling();
            if (nextSibling == null) {
                DefaultMutableTreeNode aNode = (DefaultMutableTreeNode)(DefaultMutableTreeNode)getParent();
                do {
                    if (aNode == null) {
                        return null;
                    }
                    nextSibling = aNode.getNextSibling();
                    if (nextSibling != null) {
                        return nextSibling;
                    }
                    aNode = (DefaultMutableTreeNode)(DefaultMutableTreeNode)aNode.getParent();
                }                 while (true);
            } else {
                return nextSibling;
            }
        } else {
            return (DefaultMutableTreeNode)(DefaultMutableTreeNode)getChildAt(0);
        }
    }
    
    public DefaultMutableTreeNode getPreviousNode() {
        DefaultMutableTreeNode previousSibling;
        DefaultMutableTreeNode myParent = (DefaultMutableTreeNode)(DefaultMutableTreeNode)getParent();
        if (myParent == null) {
            return null;
        }
        previousSibling = getPreviousSibling();
        if (previousSibling != null) {
            if (previousSibling.getChildCount() == 0) return previousSibling; else return previousSibling.getLastLeaf();
        } else {
            return myParent;
        }
    }
    
    public Enumeration preorderEnumeration() {
        return new DefaultMutableTreeNode$PreorderEnumeration(this, this);
    }
    
    public Enumeration postorderEnumeration() {
        return new DefaultMutableTreeNode$PostorderEnumeration(this, this);
    }
    
    public Enumeration breadthFirstEnumeration() {
        return new DefaultMutableTreeNode$BreadthFirstEnumeration(this, this);
    }
    
    public Enumeration depthFirstEnumeration() {
        return postorderEnumeration();
    }
    
    public Enumeration pathFromAncestorEnumeration(TreeNode ancestor) {
        return new DefaultMutableTreeNode$PathBetweenNodesEnumeration(this, ancestor, this);
    }
    
    public boolean isNodeChild(TreeNode aNode) {
        boolean retval;
        if (aNode == null) {
            retval = false;
        } else {
            if (getChildCount() == 0) {
                retval = false;
            } else {
                retval = (aNode.getParent() == this);
            }
        }
        return retval;
    }
    
    public TreeNode getFirstChild() {
        if (getChildCount() == 0) {
            throw new NoSuchElementException("node has no children");
        }
        return getChildAt(0);
    }
    
    public TreeNode getLastChild() {
        if (getChildCount() == 0) {
            throw new NoSuchElementException("node has no children");
        }
        return getChildAt(getChildCount() - 1);
    }
    
    public TreeNode getChildAfter(TreeNode aChild) {
        if (aChild == null) {
            throw new IllegalArgumentException("argument is null");
        }
        int index = getIndex(aChild);
        if (index == -1) {
            throw new IllegalArgumentException("node is not a child");
        }
        if (index < getChildCount() - 1) {
            return getChildAt(index + 1);
        } else {
            return null;
        }
    }
    
    public TreeNode getChildBefore(TreeNode aChild) {
        if (aChild == null) {
            throw new IllegalArgumentException("argument is null");
        }
        int index = getIndex(aChild);
        if (index == -1) {
            throw new IllegalArgumentException("argument is not a child");
        }
        if (index > 0) {
            return getChildAt(index - 1);
        } else {
            return null;
        }
    }
    
    public boolean isNodeSibling(TreeNode anotherNode) {
        boolean retval;
        if (anotherNode == null) {
            retval = false;
        } else if (anotherNode == this) {
            retval = true;
        } else {
            TreeNode myParent = getParent();
            retval = (myParent != null && myParent == anotherNode.getParent());
            if (retval && !((DefaultMutableTreeNode)(DefaultMutableTreeNode)getParent()).isNodeChild(anotherNode)) {
                throw new Error("sibling has different parent");
            }
        }
        return retval;
    }
    
    public int getSiblingCount() {
        TreeNode myParent = getParent();
        if (myParent == null) {
            return 1;
        } else {
            return myParent.getChildCount();
        }
    }
    
    public DefaultMutableTreeNode getNextSibling() {
        DefaultMutableTreeNode retval;
        DefaultMutableTreeNode myParent = (DefaultMutableTreeNode)(DefaultMutableTreeNode)getParent();
        if (myParent == null) {
            retval = null;
        } else {
            retval = (DefaultMutableTreeNode)(DefaultMutableTreeNode)myParent.getChildAfter(this);
        }
        if (retval != null && !isNodeSibling(retval)) {
            throw new Error("child of parent is not a sibling");
        }
        return retval;
    }
    
    public DefaultMutableTreeNode getPreviousSibling() {
        DefaultMutableTreeNode retval;
        DefaultMutableTreeNode myParent = (DefaultMutableTreeNode)(DefaultMutableTreeNode)getParent();
        if (myParent == null) {
            retval = null;
        } else {
            retval = (DefaultMutableTreeNode)(DefaultMutableTreeNode)myParent.getChildBefore(this);
        }
        if (retval != null && !isNodeSibling(retval)) {
            throw new Error("child of parent is not a sibling");
        }
        return retval;
    }
    
    public boolean isLeaf() {
        return (getChildCount() == 0);
    }
    
    public DefaultMutableTreeNode getFirstLeaf() {
        DefaultMutableTreeNode node = this;
        while (!node.isLeaf()) {
            node = (DefaultMutableTreeNode)(DefaultMutableTreeNode)node.getFirstChild();
        }
        return node;
    }
    
    public DefaultMutableTreeNode getLastLeaf() {
        DefaultMutableTreeNode node = this;
        while (!node.isLeaf()) {
            node = (DefaultMutableTreeNode)(DefaultMutableTreeNode)node.getLastChild();
        }
        return node;
    }
    
    public DefaultMutableTreeNode getNextLeaf() {
        DefaultMutableTreeNode nextSibling;
        DefaultMutableTreeNode myParent = (DefaultMutableTreeNode)(DefaultMutableTreeNode)getParent();
        if (myParent == null) return null;
        nextSibling = getNextSibling();
        if (nextSibling != null) return nextSibling.getFirstLeaf();
        return myParent.getNextLeaf();
    }
    
    public DefaultMutableTreeNode getPreviousLeaf() {
        DefaultMutableTreeNode previousSibling;
        DefaultMutableTreeNode myParent = (DefaultMutableTreeNode)(DefaultMutableTreeNode)getParent();
        if (myParent == null) return null;
        previousSibling = getPreviousSibling();
        if (previousSibling != null) return previousSibling.getLastLeaf();
        return myParent.getPreviousLeaf();
    }
    
    public int getLeafCount() {
        int count = 0;
        TreeNode node;
        Enumeration enum_ = breadthFirstEnumeration();
        while (enum_.hasMoreElements()) {
            node = (TreeNode)(TreeNode)enum_.nextElement();
            if (node.isLeaf()) {
                count++;
            }
        }
        if (count < 1) {
            throw new Error("tree has zero leaves");
        }
        return count;
    }
    
    public String toString() {
        if (userObject == null) {
            return null;
        } else {
            return userObject.toString();
        }
    }
    
    public Object clone() {
        DefaultMutableTreeNode newNode = null;
        try {
            newNode = (DefaultMutableTreeNode)(DefaultMutableTreeNode)super.clone();
            newNode.children = null;
            newNode.parent = null;
        } catch (CloneNotSupportedException e) {
            throw new Error(e.toString());
        }
        return newNode;
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        Object[] tValues;
        s.defaultWriteObject();
        if (userObject != null && userObject instanceof Serializable) {
            tValues = new Object[2];
            tValues[0] = "userObject";
            tValues[1] = userObject;
        } else tValues = new Object[0];
        s.writeObject(tValues);
    }
    
    private void readObject(ObjectInputStream s) throws IOException, ClassNotFoundException {
        Object[] tValues;
        s.defaultReadObject();
        tValues = (Object[])(Object[])s.readObject();
        if (tValues.length > 0 && tValues[0].equals("userObject")) userObject = tValues[1];
    }
    {
    }
    {
    }
    {
    }
    {
    }
}
