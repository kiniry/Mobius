package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.util.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.accessibility.*;

class AccessibleHTML$TableElementInfo extends AccessibleHTML$ElementInfo implements Accessible {
    
    /*synthetic*/ static AccessibleHTML.TableElementInfo.TableCellElementInfo[][] access$1200(AccessibleHTML$TableElementInfo x0) {
        return x0.grid;
    }
    /*synthetic*/ final AccessibleHTML this$0;
    protected AccessibleHTML$ElementInfo caption;
    private AccessibleHTML$TableElementInfo$TableCellElementInfo[][] grid;
    
    AccessibleHTML$TableElementInfo(/*synthetic*/ final AccessibleHTML this$0, Element e, AccessibleHTML$ElementInfo parent) {
        this.this$0 = this$0;
        super(this$0, e, parent);
    }
    
    public AccessibleHTML$ElementInfo getCaptionInfo() {
        return caption;
    }
    
    protected void validate() {
        super.validate();
        updateGrid();
    }
    
    protected void loadChildren(Element e) {
        for (int counter = 0; counter < e.getElementCount(); counter++) {
            Element child = e.getElement(counter);
            AttributeSet attrs = child.getAttributes();
            if (attrs.getAttribute(StyleConstants.NameAttribute) == HTML$Tag.TR) {
                addChild(new AccessibleHTML$TableElementInfo$TableRowElementInfo(this, child, this, counter));
            } else if (attrs.getAttribute(StyleConstants.NameAttribute) == HTML$Tag.CAPTION) {
                caption = this$0.createElementInfo(child, this);
            }
        }
    }
    
    private void updateGrid() {
        int delta = 0;
        int maxCols = 0;
        int rows = 0;
        for (int counter = 0; counter < getChildCount(); counter++) {
            AccessibleHTML$TableElementInfo$TableRowElementInfo row = getRow(counter);
            int prev = 0;
            for (int y = 0; y < delta; y++) {
                prev = Math.max(prev, AccessibleHTML.TableElementInfo.TableRowElementInfo.access$1000(getRow(counter - y - 1), y + 2));
            }
            delta = Math.max(row.getRowCount(), delta);
            delta--;
            maxCols = Math.max(maxCols, row.getColumnCount() + prev);
        }
        rows = getChildCount() + delta;
        grid = new AccessibleHTML$TableElementInfo$TableCellElementInfo[rows][];
        for (int counter = 0; counter < rows; counter++) {
            grid[counter] = new AccessibleHTML$TableElementInfo$TableCellElementInfo[maxCols];
        }
        for (int counter = 0; counter < rows; counter++) {
            AccessibleHTML.TableElementInfo.TableRowElementInfo.access$1100(getRow(counter), counter);
        }
    }
    
    public AccessibleHTML$TableElementInfo$TableRowElementInfo getRow(int index) {
        return (AccessibleHTML$TableElementInfo$TableRowElementInfo)(AccessibleHTML$TableElementInfo$TableRowElementInfo)getChild(index);
    }
    
    public AccessibleHTML$TableElementInfo$TableCellElementInfo getCell(int r, int c) {
        if (validateIfNecessary() && r < grid.length && c < grid[0].length) {
            return grid[r][c];
        }
        return null;
    }
    
    public int getRowExtentAt(int r, int c) {
        AccessibleHTML$TableElementInfo$TableCellElementInfo cell = getCell(r, c);
        if (cell != null) {
            int rows = cell.getRowCount();
            int delta = 1;
            while ((r - delta) >= 0 && grid[r - delta][c] == cell) {
                delta++;
            }
            return rows - delta + 1;
        }
        return 0;
    }
    
    public int getColumnExtentAt(int r, int c) {
        AccessibleHTML$TableElementInfo$TableCellElementInfo cell = getCell(r, c);
        if (cell != null) {
            int cols = cell.getColumnCount();
            int delta = 1;
            while ((c - delta) >= 0 && grid[r][c - delta] == cell) {
                delta++;
            }
            return cols - delta + 1;
        }
        return 0;
    }
    
    public int getRowCount() {
        if (validateIfNecessary()) {
            return grid.length;
        }
        return 0;
    }
    
    public int getColumnCount() {
        if (validateIfNecessary() && grid.length > 0) {
            return grid[0].length;
        }
        return 0;
    }
    private AccessibleContext accessibleContext;
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new AccessibleHTML$TableElementInfo$TableAccessibleContext(this, this);
        }
        return accessibleContext;
    }
    {
    }
    {
    }
    {
    }
}
