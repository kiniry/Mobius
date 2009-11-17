package java.awt.dnd;

import java.awt.Component;
import java.awt.Cursor;
import java.awt.Image;
import java.awt.Point;
import java.awt.datatransfer.Transferable;
import java.awt.dnd.DragGestureEvent;
import java.awt.dnd.DragSource;
import java.awt.dnd.DragSourceListener;
import java.awt.dnd.peer.DragSourceContextPeer;
import java.io.IOException;
import java.io.ObjectOutputStream;
import java.io.ObjectInputStream;
import java.io.Serializable;
import java.util.TooManyListenersException;

public class DragSourceContext implements DragSourceListener, DragSourceMotionListener, Serializable {
    private static final long serialVersionUID = -115407898692194719L;
    protected static final int DEFAULT = 0;
    protected static final int ENTER = 1;
    protected static final int OVER = 2;
    protected static final int CHANGED = 3;
    
    public DragSourceContext(DragSourceContextPeer dscp, DragGestureEvent trigger, Cursor dragCursor, Image dragImage, Point offset, Transferable t, DragSourceListener dsl) {
        
        if (dscp == null) {
            throw new NullPointerException("DragSourceContextPeer");
        }
        if (trigger == null) {
            throw new NullPointerException("Trigger");
        }
        if (trigger.getDragSource() == null) {
            throw new IllegalArgumentException("DragSource");
        }
        if (trigger.getComponent() == null) {
            throw new IllegalArgumentException("Component");
        }
        if (trigger.getSourceAsDragGestureRecognizer().getSourceActions() == DnDConstants.ACTION_NONE) {
            throw new IllegalArgumentException("source actions");
        }
        if (trigger.getDragAction() == DnDConstants.ACTION_NONE) {
            throw new IllegalArgumentException("no drag action");
        }
        if (t == null) {
            throw new NullPointerException("Transferable");
        }
        if (dragImage != null && offset == null) {
            throw new NullPointerException("offset");
        }
        peer = dscp;
        this.trigger = trigger;
        cursor = dragCursor;
        transferable = t;
        listener = dsl;
        sourceActions = trigger.getSourceAsDragGestureRecognizer().getSourceActions();
        useCustomCursor = (dragCursor != null);
        updateCurrentCursor(trigger.getDragAction(), getSourceActions(), DEFAULT);
    }
    
    public DragSource getDragSource() {
        return trigger.getDragSource();
    }
    
    public Component getComponent() {
        return trigger.getComponent();
    }
    
    public DragGestureEvent getTrigger() {
        return trigger;
    }
    
    public int getSourceActions() {
        return sourceActions;
    }
    
    public synchronized void setCursor(Cursor c) {
        useCustomCursor = (c != null);
        setCursorImpl(c);
    }
    
    public Cursor getCursor() {
        return cursor;
    }
    
    public synchronized void addDragSourceListener(DragSourceListener dsl) throws TooManyListenersException {
        if (dsl == null) return;
        if (equals(dsl)) throw new IllegalArgumentException("DragSourceContext may not be its own listener");
        if (listener != null) throw new TooManyListenersException(); else listener = dsl;
    }
    
    public synchronized void removeDragSourceListener(DragSourceListener dsl) {
        if (listener != null && listener.equals(dsl)) {
            listener = null;
        } else throw new IllegalArgumentException();
    }
    
    public void transferablesFlavorsChanged() {
        if (peer != null) peer.transferablesFlavorsChanged();
    }
    
    public void dragEnter(DragSourceDragEvent dsde) {
        DragSourceListener dsl = listener;
        if (dsl != null) {
            dsl.dragEnter(dsde);
        }
        getDragSource().processDragEnter(dsde);
        updateCurrentCursor(dsde.getDropAction(), dsde.getTargetActions(), ENTER);
    }
    
    public void dragOver(DragSourceDragEvent dsde) {
        DragSourceListener dsl = listener;
        if (dsl != null) {
            dsl.dragOver(dsde);
        }
        getDragSource().processDragOver(dsde);
        updateCurrentCursor(dsde.getDropAction(), dsde.getTargetActions(), OVER);
    }
    
    public void dragExit(DragSourceEvent dse) {
        DragSourceListener dsl = listener;
        if (dsl != null) {
            dsl.dragExit(dse);
        }
        getDragSource().processDragExit(dse);
        updateCurrentCursor(DnDConstants.ACTION_NONE, DnDConstants.ACTION_NONE, DEFAULT);
    }
    
    public void dropActionChanged(DragSourceDragEvent dsde) {
        DragSourceListener dsl = listener;
        if (dsl != null) {
            dsl.dropActionChanged(dsde);
        }
        getDragSource().processDropActionChanged(dsde);
        updateCurrentCursor(dsde.getDropAction(), dsde.getTargetActions(), CHANGED);
    }
    
    public void dragDropEnd(DragSourceDropEvent dsde) {
        DragSourceListener dsl = listener;
        if (dsl != null) {
            dsl.dragDropEnd(dsde);
        }
        getDragSource().processDragDropEnd(dsde);
    }
    
    public void dragMouseMoved(DragSourceDragEvent dsde) {
        getDragSource().processDragMouseMoved(dsde);
    }
    
    public Transferable getTransferable() {
        return transferable;
    }
    
    protected synchronized void updateCurrentCursor(int dropOp, int targetAct, int status) {
        if (useCustomCursor) {
            return;
        }
        Cursor c = null;
        switch (status) {
        default: 
            targetAct = DnDConstants.ACTION_NONE;
        
        case ENTER: 
        
        case OVER: 
        
        case CHANGED: 
            int ra = dropOp & targetAct;
            if (ra == DnDConstants.ACTION_NONE) {
                if ((dropOp & DnDConstants.ACTION_LINK) == DnDConstants.ACTION_LINK) c = DragSource.DefaultLinkNoDrop; else if ((dropOp & DnDConstants.ACTION_MOVE) == DnDConstants.ACTION_MOVE) c = DragSource.DefaultMoveNoDrop; else c = DragSource.DefaultCopyNoDrop;
            } else {
                if ((ra & DnDConstants.ACTION_LINK) == DnDConstants.ACTION_LINK) c = DragSource.DefaultLinkDrop; else if ((ra & DnDConstants.ACTION_MOVE) == DnDConstants.ACTION_MOVE) c = DragSource.DefaultMoveDrop; else c = DragSource.DefaultCopyDrop;
            }
        
        }
        setCursorImpl(c);
    }
    
    private void setCursorImpl(Cursor c) {
        if (cursor == null || !cursor.equals(c)) {
            cursor = c;
            if (peer != null) peer.setCursor(cursor);
        }
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        s.writeObject(SerializationTester.test(transferable) ? transferable : null);
        s.writeObject(SerializationTester.test(listener) ? listener : null);
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException {
        s.defaultReadObject();
        transferable = (Transferable)(Transferable)s.readObject();
        listener = (DragSourceListener)(DragSourceListener)s.readObject();
        if (transferable == null) {
            if (emptyTransferable == null) {
                emptyTransferable = new DragSourceContext$1(this);
            }
            transferable = emptyTransferable;
        }
    }
    private static Transferable emptyTransferable;
    private transient DragSourceContextPeer peer;
    private DragGestureEvent trigger;
    private Cursor cursor;
    private transient Transferable transferable;
    private transient DragSourceListener listener;
    private boolean useCustomCursor;
    private final int sourceActions;
}
