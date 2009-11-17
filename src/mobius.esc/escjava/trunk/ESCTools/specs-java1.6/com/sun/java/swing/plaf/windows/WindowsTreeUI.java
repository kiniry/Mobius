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

public class WindowsTreeUI extends BasicTreeUI {
    
    public WindowsTreeUI() {
        
    }
    
    public static ComponentUI createUI(JComponent c) {
        return new WindowsTreeUI();
    }
    
    protected void ensureRowsAreVisible(int beginRow, int endRow) {
        if (tree != null && beginRow >= 0 && endRow < getRowCount(tree)) {
            Rectangle visRect = tree.getVisibleRect();
            if (beginRow == endRow) {
                Rectangle scrollBounds = getPathBounds(tree, getPathForRow(tree, beginRow));
                if (scrollBounds != null) {
                    scrollBounds.x = visRect.x;
                    scrollBounds.width = visRect.width;
                    tree.scrollRectToVisible(scrollBounds);
                }
            } else {
                Rectangle beginRect = getPathBounds(tree, getPathForRow(tree, beginRow));
                Rectangle testRect = beginRect;
                int beginY = beginRect.y;
                int maxY = beginY + visRect.height;
                for (int counter = beginRow + 1; counter <= endRow; counter++) {
                    testRect = getPathBounds(tree, getPathForRow(tree, counter));
                    if ((testRect.y + testRect.height) > maxY) counter = endRow;
                }
                tree.scrollRectToVisible(new Rectangle(visRect.x, beginY, 1, testRect.y + testRect.height - beginY));
            }
        }
    }
    protected static final int HALF_SIZE = 4;
    protected static final int SIZE = 9;
    
    protected TreeCellRenderer createDefaultCellRenderer() {
        return new WindowsTreeUI$WindowsTreeCellRenderer(this);
    }
    {
    }
    {
    }
    {
    }
}
