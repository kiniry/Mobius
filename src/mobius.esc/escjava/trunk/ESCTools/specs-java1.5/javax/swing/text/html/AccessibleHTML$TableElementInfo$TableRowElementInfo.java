package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.util.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.accessibility.*;

class AccessibleHTML$TableElementInfo$TableRowElementInfo extends AccessibleHTML$ElementInfo {
    
    /*synthetic*/ static void access$1100(AccessibleHTML$TableElementInfo$TableRowElementInfo x0, int x1) {
        x0.updateGrid(x1);
    }
    
    /*synthetic*/ static int access$1000(AccessibleHTML$TableElementInfo$TableRowElementInfo x0, int x1) {
        return x0.getColumnCount(x1);
    }
    /*synthetic*/ final AccessibleHTML$TableElementInfo this$1;
    private AccessibleHTML$TableElementInfo parent;
    private int rowNumber;
    
    AccessibleHTML$TableElementInfo$TableRowElementInfo(/*synthetic*/ final AccessibleHTML$TableElementInfo this$1, Element e, AccessibleHTML$TableElementInfo parent, int rowNumber) {
        this.this$1 = this$1;
        super(this$1.this$0, e, parent);
        this.parent = parent;
        this.rowNumber = rowNumber;
    }
    
    protected void loadChildren(Element e) {
        for (int x = 0; x < e.getElementCount(); x++) {
            AttributeSet attrs = e.getElement(x).getAttributes();
            if (attrs.getAttribute(StyleConstants.NameAttribute) == HTML$Tag.TH) {
                AccessibleHTML$TableElementInfo$TableCellElementInfo headerElementInfo = new AccessibleHTML$TableElementInfo$TableCellElementInfo(this$1, e.getElement(x), this, true);
                addChild(headerElementInfo);
                AccessibleTable at = parent.getAccessibleContext().getAccessibleTable();
                AccessibleHTML$TableElementInfo$TableAccessibleContext tableElement = (AccessibleHTML$TableElementInfo$TableAccessibleContext)(AccessibleHTML$TableElementInfo$TableAccessibleContext)at;
                tableElement.addRowHeader(headerElementInfo, rowNumber);
            } else if (attrs.getAttribute(StyleConstants.NameAttribute) == HTML$Tag.TD) {
                addChild(new AccessibleHTML$TableElementInfo$TableCellElementInfo(this$1, e.getElement(x), this, false));
            }
        }
    }
    
    public int getRowCount() {
        int rowCount = 1;
        if (validateIfNecessary()) {
            for (int counter = 0; counter < getChildCount(); counter++) {
                AccessibleHTML$TableElementInfo$TableCellElementInfo cell = (AccessibleHTML$TableElementInfo$TableCellElementInfo)(AccessibleHTML$TableElementInfo$TableCellElementInfo)getChild(counter);
                if (cell.validateIfNecessary()) {
                    rowCount = Math.max(rowCount, cell.getRowCount());
                }
            }
        }
        return rowCount;
    }
    
    public int getColumnCount() {
        int colCount = 0;
        if (validateIfNecessary()) {
            for (int counter = 0; counter < getChildCount(); counter++) {
                AccessibleHTML$TableElementInfo$TableCellElementInfo cell = (AccessibleHTML$TableElementInfo$TableCellElementInfo)(AccessibleHTML$TableElementInfo$TableCellElementInfo)getChild(counter);
                if (cell.validateIfNecessary()) {
                    colCount += cell.getColumnCount();
                }
            }
        }
        return colCount;
    }
    
    protected void invalidate(boolean first) {
        super.invalidate(first);
        getParent().invalidate(true);
    }
    
    private void updateGrid(int row) {
        if (validateIfNecessary()) {
            boolean emptyRow = false;
            while (!emptyRow) {
                for (int counter = 0; counter < AccessibleHTML.TableElementInfo.access$1200(this$1)[row].length; counter++) {
                    if (AccessibleHTML.TableElementInfo.access$1200(this$1)[row][counter] == null) {
                        emptyRow = true;
                        break;
                    }
                }
                if (!emptyRow) {
                    row++;
                }
            }
            for (int col = 0, counter = 0; counter < getChildCount(); counter++) {
                AccessibleHTML$TableElementInfo$TableCellElementInfo cell = (AccessibleHTML$TableElementInfo$TableCellElementInfo)(AccessibleHTML$TableElementInfo$TableCellElementInfo)getChild(counter);
                while (AccessibleHTML.TableElementInfo.access$1200(this$1)[row][col] != null) {
                    col++;
                }
                for (int rowCount = cell.getRowCount() - 1; rowCount >= 0; rowCount--) {
                    for (int colCount = cell.getColumnCount() - 1; colCount >= 0; colCount--) {
                        AccessibleHTML.TableElementInfo.access$1200(this$1)[row + rowCount][col + colCount] = cell;
                    }
                }
                col += cell.getColumnCount();
            }
        }
    }
    
    private int getColumnCount(int rowspan) {
        if (validateIfNecessary()) {
            int cols = 0;
            for (int counter = 0; counter < getChildCount(); counter++) {
                AccessibleHTML$TableElementInfo$TableCellElementInfo cell = (AccessibleHTML$TableElementInfo$TableCellElementInfo)(AccessibleHTML$TableElementInfo$TableCellElementInfo)getChild(counter);
                if (cell.getRowCount() >= rowspan) {
                    cols += cell.getColumnCount();
                }
            }
            return cols;
        }
        return 0;
    }
}
