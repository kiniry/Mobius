package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.awt.dnd.*;
import java.beans.*;
import java.lang.reflect.*;
import java.io.*;
import java.util.TooManyListenersException;
import javax.swing.plaf.UIResource;
import javax.swing.event.*;

class TransferHandler$SwingDropTarget extends DropTarget implements UIResource {
    
    TransferHandler$SwingDropTarget(JComponent c) {
        
        setComponent(c);
        try {
            super.addDropTargetListener(TransferHandler.access$200());
        } catch (TooManyListenersException tmle) {
        }
    }
    
    public void addDropTargetListener(DropTargetListener dtl) throws TooManyListenersException {
        if (listenerList == null) {
            listenerList = new EventListenerList();
        }
        listenerList.add(DropTargetListener.class, dtl);
    }
    
    public void removeDropTargetListener(DropTargetListener dtl) {
        if (listenerList != null) {
            listenerList.remove(DropTargetListener.class, dtl);
        }
    }
    
    public void dragEnter(DropTargetDragEvent e) {
        super.dragEnter(e);
        if (listenerList != null) {
            Object[] listeners = listenerList.getListenerList();
            for (int i = listeners.length - 2; i >= 0; i -= 2) {
                if (listeners[i] == DropTargetListener.class) {
                    ((DropTargetListener)(DropTargetListener)listeners[i + 1]).dragEnter(e);
                }
            }
        }
    }
    
    public void dragOver(DropTargetDragEvent e) {
        super.dragOver(e);
        if (listenerList != null) {
            Object[] listeners = listenerList.getListenerList();
            for (int i = listeners.length - 2; i >= 0; i -= 2) {
                if (listeners[i] == DropTargetListener.class) {
                    ((DropTargetListener)(DropTargetListener)listeners[i + 1]).dragOver(e);
                }
            }
        }
    }
    
    public void dragExit(DropTargetEvent e) {
        super.dragExit(e);
        if (listenerList != null) {
            Object[] listeners = listenerList.getListenerList();
            for (int i = listeners.length - 2; i >= 0; i -= 2) {
                if (listeners[i] == DropTargetListener.class) {
                    ((DropTargetListener)(DropTargetListener)listeners[i + 1]).dragExit(e);
                }
            }
        }
    }
    
    public void drop(DropTargetDropEvent e) {
        super.drop(e);
        if (listenerList != null) {
            Object[] listeners = listenerList.getListenerList();
            for (int i = listeners.length - 2; i >= 0; i -= 2) {
                if (listeners[i] == DropTargetListener.class) {
                    ((DropTargetListener)(DropTargetListener)listeners[i + 1]).drop(e);
                }
            }
        }
    }
    
    public void dropActionChanged(DropTargetDragEvent e) {
        super.dropActionChanged(e);
        if (listenerList != null) {
            Object[] listeners = listenerList.getListenerList();
            for (int i = listeners.length - 2; i >= 0; i -= 2) {
                if (listeners[i] == DropTargetListener.class) {
                    ((DropTargetListener)(DropTargetListener)listeners[i + 1]).dropActionChanged(e);
                }
            }
        }
    }
    private EventListenerList listenerList;
}
