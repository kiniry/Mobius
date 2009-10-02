package javax.swing;

import java.awt.event.*;
import java.awt.*;
import java.util.Vector;
import java.beans.*;
import javax.swing.event.*;
import javax.accessibility.*;
import javax.swing.plaf.*;

class JList$5 extends AbstractListModel {
    /*synthetic*/ final JList this$0;
    /*synthetic*/ final Vector val$listData;
    
    JList$5(/*synthetic*/ final JList this$0, /*synthetic*/ final Vector val$listData) {
        this.this$0 = this$0;
        this.val$listData = val$listData;
        
    }
    
    public int getSize() {
        return val$listData.size();
    }
    
    public Object getElementAt(int i) {
        return val$listData.elementAt(i);
    }
}
