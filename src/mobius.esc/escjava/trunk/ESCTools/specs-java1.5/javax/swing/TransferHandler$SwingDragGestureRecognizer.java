package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.awt.dnd.*;
import java.beans.*;
import java.lang.reflect.*;
import java.io.*;
import javax.swing.event.*;

class TransferHandler$SwingDragGestureRecognizer extends DragGestureRecognizer {
    
    TransferHandler$SwingDragGestureRecognizer(DragGestureListener dgl) {
        super(DragSource.getDefaultDragSource(), null, 0, dgl);
    }
    
    void gestured(JComponent c, MouseEvent e, int srcActions, int action) {
        setComponent(c);
        setSourceActions(srcActions);
        appendEvent(e);
        fireDragGestureRecognized(action, e.getPoint());
    }
    
    protected void registerListeners() {
    }
    
    protected void unregisterListeners() {
    }
}
