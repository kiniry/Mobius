package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.util.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.accessibility.*;

class AccessibleHTML$TableElementInfo$TableCellElementInfo extends AccessibleHTML$ElementInfo {
    /*synthetic*/ final AccessibleHTML$TableElementInfo this$1;
    private Accessible accessible;
    private boolean isHeaderCell;
    
    AccessibleHTML$TableElementInfo$TableCellElementInfo(/*synthetic*/ final AccessibleHTML$TableElementInfo this$1, Element e, AccessibleHTML$ElementInfo parent) {
        this.this$1 = this$1;
        super(this$1.this$0, e, parent);
        this.isHeaderCell = false;
    }
    
    AccessibleHTML$TableElementInfo$TableCellElementInfo(/*synthetic*/ final AccessibleHTML$TableElementInfo this$1, Element e, AccessibleHTML$ElementInfo parent, boolean isHeaderCell) {
        this.this$1 = this$1;
        super(this$1.this$0, e, parent);
        this.isHeaderCell = isHeaderCell;
    }
    
    public boolean isHeaderCell() {
        return this.isHeaderCell;
    }
    
    public Accessible getAccessible() {
        accessible = null;
        getAccessible(this);
        return accessible;
    }
    
    private void getAccessible(AccessibleHTML$ElementInfo elementInfo) {
        if (elementInfo instanceof Accessible) {
            accessible = (Accessible)(Accessible)elementInfo;
            return;
        } else {
            for (int i = 0; i < elementInfo.getChildCount(); i++) {
                getAccessible(elementInfo.getChild(i));
            }
        }
    }
    
    public int getRowCount() {
        if (validateIfNecessary()) {
            return Math.max(1, getIntAttr(getAttributes(), HTML$Attribute.ROWSPAN, 1));
        }
        return 0;
    }
    
    public int getColumnCount() {
        if (validateIfNecessary()) {
            return Math.max(1, getIntAttr(getAttributes(), HTML$Attribute.COLSPAN, 1));
        }
        return 0;
    }
    
    protected void invalidate(boolean first) {
        super.invalidate(first);
        getParent().invalidate(true);
    }
}
