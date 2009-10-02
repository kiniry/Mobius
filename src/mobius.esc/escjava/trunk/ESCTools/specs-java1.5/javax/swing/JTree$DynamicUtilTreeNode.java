package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.io.*;
import java.util.*;
import javax.swing.event.*;
import javax.swing.tree.*;
import javax.accessibility.*;

public class JTree$DynamicUtilTreeNode extends DefaultMutableTreeNode {
    protected boolean hasChildren;
    protected Object childValue;
    protected boolean loadedChildren;
    
    public static void createChildren(DefaultMutableTreeNode parent, Object children) {
        if (children instanceof Vector) {
            Vector childVector = (Vector)(Vector)children;
            for (int counter = 0, maxCounter = childVector.size(); counter < maxCounter; counter++) parent.add(new JTree$DynamicUtilTreeNode(childVector.elementAt(counter), childVector.elementAt(counter)));
        } else if (children instanceof Hashtable) {
            Hashtable childHT = (Hashtable)(Hashtable)children;
            Enumeration keys = childHT.keys();
            Object aKey;
            while (keys.hasMoreElements()) {
                aKey = keys.nextElement();
                parent.add(new JTree$DynamicUtilTreeNode(aKey, childHT.get(aKey)));
            }
        } else if (children instanceof Object[]) {
            Object[] childArray = (Object[])(Object[])children;
            for (int counter = 0, maxCounter = childArray.length; counter < maxCounter; counter++) parent.add(new JTree$DynamicUtilTreeNode(childArray[counter], childArray[counter]));
        }
    }
    
    public JTree$DynamicUtilTreeNode(Object value, Object children) {
        super(value);
        loadedChildren = false;
        childValue = children;
        if (children != null) {
            if (children instanceof Vector) setAllowsChildren(true); else if (children instanceof Hashtable) setAllowsChildren(true); else if (children instanceof Object[]) setAllowsChildren(true); else setAllowsChildren(false);
        } else setAllowsChildren(false);
    }
    
    public boolean isLeaf() {
        return !getAllowsChildren();
    }
    
    public int getChildCount() {
        if (!loadedChildren) loadChildren();
        return super.getChildCount();
    }
    
    protected void loadChildren() {
        loadedChildren = true;
        createChildren(this, childValue);
    }
    
    public TreeNode getChildAt(int index) {
        if (!loadedChildren) loadChildren();
        return super.getChildAt(index);
    }
    
    public Enumeration children() {
        if (!loadedChildren) loadChildren();
        return super.children();
    }
}
