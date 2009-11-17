package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.util.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.accessibility.*;

public class AccessibleHTML$TableElementInfo$TableAccessibleContext$AccessibleHeadersTable implements AccessibleTable {
    /*synthetic*/ final AccessibleHTML$TableElementInfo$TableAccessibleContext this$2;
    
    protected AccessibleHTML$TableElementInfo$TableAccessibleContext$AccessibleHeadersTable(/*synthetic*/ final AccessibleHTML$TableElementInfo$TableAccessibleContext this$2) {
        this.this$2 = this$2;
        
    }
    private Hashtable headers = new Hashtable();
    private int rowCount = 0;
    private int columnCount = 0;
    
    public void addHeader(AccessibleHTML$TableElementInfo$TableCellElementInfo cellInfo, int rowNumber) {
        Integer rowInteger = new Integer(rowNumber);
        ArrayList list = (ArrayList)(ArrayList)headers.get(rowInteger);
        if (list == null) {
            list = new ArrayList();
            headers.put(rowInteger, list);
        }
        list.add(cellInfo);
    }
    
    public Accessible getAccessibleCaption() {
        return null;
    }
    
    public void setAccessibleCaption(Accessible a) {
    }
    
    public Accessible getAccessibleSummary() {
        return null;
    }
    
    public void setAccessibleSummary(Accessible a) {
    }
    
    public int getAccessibleRowCount() {
        return rowCount;
    }
    
    public int getAccessibleColumnCount() {
        return columnCount;
    }
    
    private AccessibleHTML$TableElementInfo$TableCellElementInfo getElementInfoAt(int r, int c) {
        ArrayList list = (ArrayList)(ArrayList)headers.get(new Integer(r));
        if (list != null) {
            return (AccessibleHTML$TableElementInfo$TableCellElementInfo)(AccessibleHTML$TableElementInfo$TableCellElementInfo)list.get(c);
        } else {
            return null;
        }
    }
    
    public Accessible getAccessibleAt(int r, int c) {
        AccessibleHTML$ElementInfo elementInfo = getElementInfoAt(r, c);
        if (elementInfo instanceof Accessible) {
            return (Accessible)(Accessible)elementInfo;
        } else {
            return null;
        }
    }
    
    public int getAccessibleRowExtentAt(int r, int c) {
        AccessibleHTML$TableElementInfo$TableCellElementInfo elementInfo = getElementInfoAt(r, c);
        if (elementInfo != null) {
            return elementInfo.getRowCount();
        } else {
            return 0;
        }
    }
    
    public int getAccessibleColumnExtentAt(int r, int c) {
        AccessibleHTML$TableElementInfo$TableCellElementInfo elementInfo = getElementInfoAt(r, c);
        if (elementInfo != null) {
            return elementInfo.getRowCount();
        } else {
            return 0;
        }
    }
    
    public AccessibleTable getAccessibleRowHeader() {
        return null;
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
        return false;
    }
    
    public boolean isAccessibleRowSelected(int r) {
        return false;
    }
    
    public boolean isAccessibleColumnSelected(int c) {
        return false;
    }
    
    public int[] getSelectedAccessibleRows() {
        return new int[0];
    }
    
    public int[] getSelectedAccessibleColumns() {
        return new int[0];
    }
}
