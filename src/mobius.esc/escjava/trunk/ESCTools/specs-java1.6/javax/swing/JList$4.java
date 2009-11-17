package javax.swing;

import java.awt.event.*;
import java.awt.*;
import java.beans.*;
import javax.swing.event.*;
import javax.accessibility.*;
import javax.swing.plaf.*;

class JList$4 extends AbstractListModel {
    /*synthetic*/ final JList this$0;
    /*synthetic*/ final Object[] val$listData;
    
    JList$4(/*synthetic*/ final JList this$0, /*synthetic*/ final Object[] val$listData) {
        this.this$0 = this$0;
        this.val$listData = val$listData;
        
    }
    
    public int getSize() {
        return val$listData.length;
    }
    
    public Object getElementAt(int i) {
        return val$listData[i];
    }
}
