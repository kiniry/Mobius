package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.util.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.accessibility.*;

public class AccessibleHTML$TableElementInfo$TableAccessibleContext extends AccessibleHTML$HTMLAccessibleContext implements AccessibleTable {
    /*synthetic*/ final AccessibleHTML$TableElementInfo this$1;
    private AccessibleHTML$TableElementInfo$TableAccessibleContext$AccessibleHeadersTable rowHeadersTable;
    
    public AccessibleHTML$TableElementInfo$TableAccessibleContext(/*synthetic*/ final AccessibleHTML$TableElementInfo this$1, AccessibleHTML$ElementInfo elementInfo) {
        super(this$1.this$0, elementInfo);
        this.this$1 = this$1;
    }
    
    public String getAccessibleName() {
        return getAccessibleRole().toString();
    }
    
    public String getAccessibleDescription() {
        return AccessibleHTML.access$300(this$1.this$0).getContentType();
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.TABLE;
    }
    
    public int getAccessibleIndexInParent() {
        return elementInfo.getIndexInParent();
    }
    
    public int getAccessibleChildrenCount() {
        return ((AccessibleHTML$TableElementInfo)(AccessibleHTML$TableElementInfo)elementInfo).getRowCount() * ((AccessibleHTML$TableElementInfo)(AccessibleHTML$TableElementInfo)elementInfo).getColumnCount();
    }
    
    public Accessible getAccessibleChild(int i) {
        int rowCount = ((AccessibleHTML$TableElementInfo)(AccessibleHTML$TableElementInfo)elementInfo).getRowCount();
        int columnCount = ((AccessibleHTML$TableElementInfo)(AccessibleHTML$TableElementInfo)elementInfo).getColumnCount();
        int r = i / rowCount;
        int c = i % columnCount;
        if (r < 0 || r >= rowCount || c < 0 || c >= columnCount) {
            return null;
        } else {
            return getAccessibleAt(r, c);
        }
    }
    
    public AccessibleTable getAccessibleTable() {
        return this;
    }
    
    public Accessible getAccessibleCaption() {
        AccessibleHTML$ElementInfo captionInfo = this$1.getCaptionInfo();
        if (captionInfo instanceof Accessible) {
            return (Accessible)(Accessible)this$1.caption;
        } else {
            return null;
        }
    }
    
    public void setAccessibleCaption(Accessible a) {
    }
    
    public Accessible getAccessibleSummary() {
        return null;
    }
    
    public void setAccessibleSummary(Accessible a) {
    }
    
    public int getAccessibleRowCount() {
        return ((AccessibleHTML$TableElementInfo)(AccessibleHTML$TableElementInfo)elementInfo).getRowCount();
    }
    
    public int getAccessibleColumnCount() {
        return ((AccessibleHTML$TableElementInfo)(AccessibleHTML$TableElementInfo)elementInfo).getColumnCount();
    }
    
    public Accessible getAccessibleAt(int r, int c) {
        AccessibleHTML$TableElementInfo$TableCellElementInfo cellInfo = this$1.getCell(r, c);
        if (cellInfo != null) {
            return cellInfo.getAccessible();
        } else {
            return null;
        }
    }
    
    public int getAccessibleRowExtentAt(int r, int c) {
        return ((AccessibleHTML$TableElementInfo)(AccessibleHTML$TableElementInfo)elementInfo).getRowExtentAt(r, c);
    }
    
    public int getAccessibleColumnExtentAt(int r, int c) {
        return ((AccessibleHTML$TableElementInfo)(AccessibleHTML$TableElementInfo)elementInfo).getColumnExtentAt(r, c);
    }
    
    public AccessibleTable getAccessibleRowHeader() {
        return rowHeadersTable;
    }
    
    public void setAccessibleRowHeader(AccessibleTable table) {
    }
    
    public AccessibleTable getAccessibleColumnHeader() {
        return null;
    }
    
    public void setAccessibleColumnHeader(AccessibleTable table) {
    }
    
    public Accessible getAccessibleRowDescription(int r) {
        return null;
    }
    
    public void setAccessibleRowDescription(int r, Accessible a) {
    }
    
    public Accessible getAccessibleColumnDescription(int c) {
        return null;
    }
    
    public void setAccessibleColumnDescription(int c, Accessible a) {
    }
    
    public boolean isAccessibleSelected(int r, int c) {
        if (this$1.validateIfNecessary()) {
            if (r < 0 || r >= getAccessibleRowCount() || c < 0 || c >= getAccessibleColumnCount()) {
                return false;
            }
            AccessibleHTML$TableElementInfo$TableCellElementInfo cell = this$1.getCell(r, c);
            if (cell != null) {
                Element elem = cell.getElement();
                int start = elem.getStartOffset();
                int end = elem.getEndOffset();
                return start >= AccessibleHTML.access$300(this$1.this$0).getSelectionStart() && end <= AccessibleHTML.access$300(this$1.this$0).getSelectionEnd();
            }
        }
        return false;
    }
    
    public boolean isAccessibleRowSelected(int r) {
        if (this$1.validateIfNecessary()) {
            if (r < 0 || r >= getAccessibleRowCount()) {
                return false;
            }
            int nColumns = getAccessibleColumnCount();
            AccessibleHTML$TableElementInfo$TableCellElementInfo startCell = this$1.getCell(r, 0);
            if (startCell == null) {
                return false;
            }
            int start = startCell.getElement().getStartOffset();
            AccessibleHTML$TableElementInfo$TableCellElementInfo endCell = this$1.getCell(r, nColumns - 1);
            if (endCell == null) {
                return false;
            }
            int end = endCell.getElement().getEndOffset();
            return start >= AccessibleHTML.access$300(this$1.this$0).getSelectionStart() && end <= AccessibleHTML.access$300(this$1.this$0).getSelectionEnd();
        }
        return false;
    }
    
    public boolean isAccessibleColumnSelected(int c) {
        if (this$1.validateIfNecessary()) {
            if (c < 0 || c >= getAccessibleColumnCount()) {
                return false;
            }
            int nRows = getAccessibleRowCount();
            AccessibleHTML$TableElementInfo$TableCellElementInfo startCell = this$1.getCell(0, c);
            if (startCell == null) {
                return false;
            }
            int start = startCell.getElement().getStartOffset();
            AccessibleHTML$TableElementInfo$TableCellElementInfo endCell = this$1.getCell(nRows - 1, c);
            if (endCell == null) {
                return false;
            }
            int end = endCell.getElement().getEndOffset();
            return start >= AccessibleHTML.access$300(this$1.this$0).getSelectionStart() && end <= AccessibleHTML.access$300(this$1.this$0).getSelectionEnd();
        }
        return false;
    }
    
    public int[] getSelectedAccessibleRows() {
        if (this$1.validateIfNecessary()) {
            int nRows = getAccessibleRowCount();
            Vector vec = new Vector();
            for (int i = 0; i < nRows; i++) {
                if (isAccessibleRowSelected(i)) {
                    vec.addElement(new Integer(i));
                }
            }
            int[] retval = new int[vec.size()];
            for (int i = 0; i < retval.length; i++) {
                retval[i] = ((Integer)(Integer)vec.elementAt(i)).intValue();
            }
            return retval;
        }
        return new int[0];
    }
    
    public int[] getSelectedAccessibleColumns() {
        if (this$1.validateIfNecessary()) {
            int nColumns = getAccessibleRowCount();
            Vector vec = new Vector();
            for (int i = 0; i < nColumns; i++) {
                if (isAccessibleColumnSelected(i)) {
                    vec.addElement(new Integer(i));
                }
            }
            int[] retval = new int[vec.size()];
            for (int i = 0; i < retval.length; i++) {
                retval[i] = ((Integer)(Integer)vec.elementAt(i)).intValue();
            }
            return retval;
        }
        return new int[0];
    }
    
    public int getAccessibleRow(int index) {
        if (this$1.validateIfNecessary()) {
            int numCells = getAccessibleColumnCount() * getAccessibleRowCount();
            if (index >= numCells) {
                return -1;
            } else {
                return index / getAccessibleColumnCount();
            }
        }
        return -1;
    }
    
    public int getAccessibleColumn(int index) {
        if (this$1.validateIfNecessary()) {
            int numCells = getAccessibleColumnCount() * getAccessibleRowCount();
            if (index >= numCells) {
                return -1;
            } else {
                return index % getAccessibleColumnCount();
            }
        }
        return -1;
    }
    
    public int getAccessibleIndex(int r, int c) {
        if (this$1.validateIfNecessary()) {
            if (r >= getAccessibleRowCount() || c >= getAccessibleColumnCount()) {
                return -1;
            } else {
                return r * getAccessibleColumnCount() + c;
            }
        }
        return -1;
    }
    
    public String getAccessibleRowHeader(int r) {
        if (this$1.validateIfNecessary()) {
            AccessibleHTML$TableElementInfo$TableCellElementInfo cellInfo = this$1.getCell(r, 0);
            if (cellInfo.isHeaderCell()) {
                View v = cellInfo.getView();
                if (v != null && AccessibleHTML.access$200(this$1.this$0) != null) {
                    try {
                        return AccessibleHTML.access$200(this$1.this$0).getText(v.getStartOffset(), v.getEndOffset() - v.getStartOffset());
                    } catch (BadLocationException e) {
                        return null;
                    }
                }
            }
        }
        return null;
    }
    
    public String getAccessibleColumnHeader(int c) {
        if (this$1.validateIfNecessary()) {
            AccessibleHTML$TableElementInfo$TableCellElementInfo cellInfo = this$1.getCell(0, c);
            if (cellInfo.isHeaderCell()) {
                View v = cellInfo.getView();
                if (v != null && AccessibleHTML.access$200(this$1.this$0) != null) {
                    try {
                        return AccessibleHTML.access$200(this$1.this$0).getText(v.getStartOffset(), v.getEndOffset() - v.getStartOffset());
                    } catch (BadLocationException e) {
                        return null;
                    }
                }
            }
        }
        return null;
    }
    
    public void addRowHeader(AccessibleHTML$TableElementInfo$TableCellElementInfo cellInfo, int rowNumber) {
        if (rowHeadersTable == null) {
            rowHeadersTable = new AccessibleHTML$TableElementInfo$TableAccessibleContext$AccessibleHeadersTable(this);
        }
        rowHeadersTable.addHeader(cellInfo, rowNumber);
    }
    {
    }
}
