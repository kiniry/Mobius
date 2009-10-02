package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.awt.dnd.*;
import java.beans.*;
import java.lang.reflect.*;
import java.io.*;
import javax.swing.event.*;

class TransferHandler$DragHandler implements DragGestureListener, DragSourceListener {
    
    /*synthetic*/ TransferHandler$DragHandler(javax.swing.TransferHandler$1 x0) {
        this();
    }
    
    private TransferHandler$DragHandler() {
        
    }
    private boolean scrolls;
    
    public void dragGestureRecognized(DragGestureEvent dge) {
        JComponent c = (JComponent)(JComponent)dge.getComponent();
        TransferHandler th = c.getTransferHandler();
        Transferable t = th.createTransferable(c);
        if (t != null) {
            scrolls = c.getAutoscrolls();
            c.setAutoscrolls(false);
            try {
                dge.startDrag(null, t, this);
                return;
            } catch (RuntimeException re) {
                c.setAutoscrolls(scrolls);
            }
        }
        th.exportDone(c, t, 0);
    }
    
    public void dragEnter(DragSourceDragEvent dsde) {
    }
    
    public void dragOver(DragSourceDragEvent dsde) {
    }
    
    public void dragExit(DragSourceEvent dsde) {
    }
    
    public void dragDropEnd(DragSourceDropEvent dsde) {
        DragSourceContext dsc = dsde.getDragSourceContext();
        JComponent c = (JComponent)(JComponent)dsc.getComponent();
        if (dsde.getDropSuccess()) {
            c.getTransferHandler().exportDone(c, dsc.getTransferable(), dsde.getDropAction());
        } else {
            c.getTransferHandler().exportDone(c, dsc.getTransferable(), 0);
        }
        c.setAutoscrolls(scrolls);
    }
    
    public void dropActionChanged(DragSourceDragEvent dsde) {
    }
}
