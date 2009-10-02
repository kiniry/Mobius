package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.awt.dnd.*;
import java.beans.*;
import java.lang.reflect.*;
import java.io.*;
import javax.swing.event.*;

class TransferHandler$DropHandler implements DropTargetListener, Serializable {
    
    /*synthetic*/ TransferHandler$DropHandler(javax.swing.TransferHandler$1 x0) {
        this();
    }
    
    private TransferHandler$DropHandler() {
        
    }
    private boolean canImport;
    
    private boolean actionSupported(int action) {
        return (action & (3 | 1073741824)) != 0;
    }
    
    public void dragEnter(DropTargetDragEvent e) {
        DataFlavor[] flavors = e.getCurrentDataFlavors();
        JComponent c = (JComponent)(JComponent)e.getDropTargetContext().getComponent();
        TransferHandler importer = c.getTransferHandler();
        if (importer != null && importer.canImport(c, flavors)) {
            canImport = true;
        } else {
            canImport = false;
        }
        int dropAction = e.getDropAction();
        if (canImport && actionSupported(dropAction)) {
            e.acceptDrag(dropAction);
        } else {
            e.rejectDrag();
        }
    }
    
    public void dragOver(DropTargetDragEvent e) {
        int dropAction = e.getDropAction();
        if (canImport && actionSupported(dropAction)) {
            e.acceptDrag(dropAction);
        } else {
            e.rejectDrag();
        }
    }
    
    public void dragExit(DropTargetEvent e) {
    }
    
    public void drop(DropTargetDropEvent e) {
        int dropAction = e.getDropAction();
        JComponent c = (JComponent)(JComponent)e.getDropTargetContext().getComponent();
        TransferHandler importer = c.getTransferHandler();
        if (canImport && importer != null && actionSupported(dropAction)) {
            e.acceptDrop(dropAction);
            try {
                Transferable t = e.getTransferable();
                e.dropComplete(importer.importData(c, t));
            } catch (RuntimeException re) {
                e.dropComplete(false);
            }
        } else {
            e.rejectDrop();
        }
    }
    
    public void dropActionChanged(DropTargetDragEvent e) {
        int dropAction = e.getDropAction();
        if (canImport && actionSupported(dropAction)) {
            e.acceptDrag(dropAction);
        } else {
            e.rejectDrag();
        }
    }
}
