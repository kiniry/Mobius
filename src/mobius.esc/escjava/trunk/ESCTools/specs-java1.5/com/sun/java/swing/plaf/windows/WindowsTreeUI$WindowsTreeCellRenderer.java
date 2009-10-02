package com.sun.java.swing.plaf.windows;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import java.util.*;
import javax.swing.plaf.basic.*;
import javax.swing.*;
import javax.swing.plaf.*;
import javax.swing.tree.*;
import com.sun.java.swing.plaf.windows.TMSchema.*;

public class WindowsTreeUI$WindowsTreeCellRenderer extends DefaultTreeCellRenderer {
    /*synthetic*/ final WindowsTreeUI this$0;
    
    public WindowsTreeUI$WindowsTreeCellRenderer(/*synthetic*/ final WindowsTreeUI this$0) {
        this.this$0 = this$0;
        
    }
    
    public Component getTreeCellRendererComponent(JTree tree, Object value, boolean sel, boolean expanded, boolean leaf, int row, boolean hasFocus) {
        super.getTreeCellRendererComponent(tree, value, sel, expanded, leaf, row, hasFocus);
        if (!tree.isEnabled()) {
            setEnabled(false);
            if (leaf) {
                setDisabledIcon(getLeafIcon());
            } else if (sel) {
                setDisabledIcon(getOpenIcon());
            } else {
                setDisabledIcon(getClosedIcon());
            }
        } else {
            setEnabled(true);
            if (leaf) {
                setIcon(getLeafIcon());
            } else if (sel) {
                setIcon(getOpenIcon());
            } else {
                setIcon(getClosedIcon());
            }
        }
        return this;
    }
}
