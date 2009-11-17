package javax.swing;

import java.awt.event.*;
import java.awt.*;
import java.beans.*;
import javax.swing.event.*;
import javax.accessibility.*;
import javax.swing.plaf.*;

class JList$1 extends AbstractListModel {
    /*synthetic*/ final Object[] val$listData;
    
    JList$1(/*synthetic*/ final Object[] val$listData) {
        this.val$listData = val$listData;
        
    }
    
    public int getSize() {
        return val$listData.length;
    }
    
    public Object getElementAt(int i) {
        return val$listData[i];
    }
}
