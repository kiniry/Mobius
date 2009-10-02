package javax.swing.tree;

import javax.swing.*;
import javax.swing.border.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.io.*;
import java.util.EventObject;

class DefaultTreeCellEditor$1 extends DefaultCellEditor {
    /*synthetic*/ final DefaultTreeCellEditor this$0;
    
    DefaultTreeCellEditor$1(/*synthetic*/ final DefaultTreeCellEditor this$0, .javax.swing.JTextField x0) {
        this.this$0 = this$0;
        super(x0);
    }
    
    public boolean shouldSelectCell(EventObject event) {
        boolean retValue = super.shouldSelectCell(event);
        return retValue;
    }
}
