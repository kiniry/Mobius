package javax.swing;

import java.awt.event.*;
import java.awt.*;
import java.util.Vector;
import java.beans.*;
import javax.swing.event.*;
import javax.accessibility.*;
import javax.swing.plaf.*;

class JList$2 extends AbstractListModel {
    /*synthetic*/ final Vector val$listData;
    
    JList$2(/*synthetic*/ final Vector val$listData) {
        this.val$listData = val$listData;
        
    }
    
    public int getSize() {
        return val$listData.size();
    }
    
    public Object getElementAt(int i) {
        return val$listData.elementAt(i);
    }
}
