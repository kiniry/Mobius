package java.awt.dnd;

import java.awt.Component;
import java.awt.Cursor;
import java.awt.GraphicsEnvironment;
import java.awt.HeadlessException;
import java.awt.Image;
import java.awt.Point;
import java.awt.Toolkit;
import java.awt.datatransfer.FlavorMap;
import java.awt.datatransfer.SystemFlavorMap;
import java.awt.datatransfer.Transferable;
import java.awt.dnd.peer.DragSourceContextPeer;
import java.io.Serializable;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.security.AccessController;
import java.util.EventListener;
import sun.awt.dnd.SunDragSourceContextPeer;
import sun.security.action.GetIntegerAction;

public class DragSource implements Serializable {
    private static final long serialVersionUID = 6236096958971414066L;
    
    private static Cursor load(String name) {
        if (GraphicsEnvironment.isHeadless()) {
            return null;
        }
        try {
            return (Cursor)(Cursor)Toolkit.getDefaultToolkit().getDesktopProperty(name);
        } catch (Exception e) {
            e.printStackTrace();
            throw new RuntimeException("failed to load system cursor: " + name + " : " + e.getMessage());
        }
    }
    public static final Cursor DefaultCopyDrop = load("DnD.Cursor.CopyDrop");
    public static final Cursor DefaultMoveDrop = load("DnD.Cursor.MoveDrop");
    public static final Cursor DefaultLinkDrop = load("DnD.Cursor.LinkDrop");
    public static final Cursor DefaultCopyNoDrop = load("DnD.Cursor.CopyNoDrop");
    public static final Cursor DefaultMoveNoDrop = load("DnD.Cursor.MoveNoDrop");
    public static final Cursor DefaultLinkNoDrop = load("DnD.Cursor.LinkNoDrop");
    private static final DragSource dflt = (GraphicsEnvironment.isHeadless()) ? null : new DragSource();
    static final String dragSourceListenerK = "dragSourceL";
    static final String dragSourceMotionListenerK = "dragSourceMotionL";
    
    public static DragSource getDefaultDragSource() {
        if (GraphicsEnvironment.isHeadless()) {
            throw new HeadlessException();
        } else {
            return dflt;
        }
    }
    
    public static boolean isDragImageSupported() {
        Toolkit t = Toolkit.getDefaultToolkit();
        Boolean supported;
        try {
            supported = (Boolean)(Boolean)Toolkit.getDefaultToolkit().getDesktopProperty("DnD.isDragImageSupported");
            return supported.booleanValue();
        } catch (Exception e) {
            return false;
        }
    }
    
    public DragSource() throws HeadlessException {
        
        if (GraphicsEnvironment.isHeadless()) {
            throw new HeadlessException();
        }
    }
    
    public void startDrag(DragGestureEvent trigger, Cursor dragCursor, Image dragImage, Point imageOffset, Transferable transferable, DragSourceListener dsl, FlavorMap flavorMap) throws InvalidDnDOperationException {
        SunDragSourceContextPeer.setDragDropInProgress(true);
        try {
            if (flavorMap != null) this.flavorMap = flavorMap;
            DragSourceContextPeer dscp = Toolkit.getDefaultToolkit().createDragSourceContextPeer(trigger);
            DragSourceContext dsc = createDragSourceContext(dscp, trigger, dragCursor, dragImage, imageOffset, transferable, dsl);
            if (dsc == null) {
                throw new InvalidDnDOperationException();
            }
            dscp.startDrag(dsc, dsc.getCursor(), dragImage, imageOffset);
        } catch (RuntimeException e) {
            SunDragSourceContextPeer.setDragDropInProgress(false);
            throw e;
        }
    }
    
    public void startDrag(DragGestureEvent trigger, Cursor dragCursor, Transferable transferable, DragSourceListener dsl, FlavorMap flavorMap) throws InvalidDnDOperationException {
        startDrag(trigger, dragCursor, null, null, transferable, dsl, flavorMap);
    }
    
    public void startDrag(DragGestureEvent trigger, Cursor dragCursor, Image dragImage, Point dragOffset, Transferable transferable, DragSourceListener dsl) throws InvalidDnDOperationException {
        startDrag(trigger, dragCursor, dragImage, dragOffset, transferable, dsl, null);
    }
    
    public void startDrag(DragGestureEvent trigger, Cursor dragCursor, Transferable transferable, DragSourceListener dsl) throws InvalidDnDOperationException {
        startDrag(trigger, dragCursor, null, null, transferable, dsl, null);
    }
    
    protected DragSourceContext createDragSourceContext(DragSourceContextPeer dscp, DragGestureEvent dgl, Cursor dragCursor, Image dragImage, Point imageOffset, Transferable t, DragSourceListener dsl) {
        return new DragSourceContext(dscp, dgl, dragCursor, dragImage, imageOffset, t, dsl);
    }
    
    public FlavorMap getFlavorMap() {
        return flavorMap;
    }
    
    public DragGestureRecognizer createDragGestureRecognizer(Class recognizerAbstractClass, Component c, int actions, DragGestureListener dgl) {
        return Toolkit.getDefaultToolkit().createDragGestureRecognizer(recognizerAbstractClass, this, c, actions, dgl);
    }
    
    public DragGestureRecognizer createDefaultDragGestureRecognizer(Component c, int actions, DragGestureListener dgl) {
        return Toolkit.getDefaultToolkit().createDragGestureRecognizer(MouseDragGestureRecognizer.class, this, c, actions, dgl);
    }
    
    public void addDragSourceListener(DragSourceListener dsl) {
        if (dsl != null) {
            synchronized (this) {
                listener = DnDEventMulticaster.add(listener, dsl);
            }
        }
    }
    
    public void removeDragSourceListener(DragSourceListener dsl) {
        if (dsl != null) {
            synchronized (this) {
                listener = DnDEventMulticaster.remove(listener, dsl);
            }
        }
    }
    
    public DragSourceListener[] getDragSourceListeners() {
        return (DragSourceListener[])(DragSourceListener[])getListeners(DragSourceListener.class);
    }
    
    public void addDragSourceMotionListener(DragSourceMotionListener dsml) {
        if (dsml != null) {
            synchronized (this) {
                motionListener = DnDEventMulticaster.add(motionListener, dsml);
            }
        }
    }
    
    public void removeDragSourceMotionListener(DragSourceMotionListener dsml) {
        if (dsml != null) {
            synchronized (this) {
                motionListener = DnDEventMulticaster.remove(motionListener, dsml);
            }
        }
    }
    
    public DragSourceMotionListener[] getDragSourceMotionListeners() {
        return (DragSourceMotionListener[])(DragSourceMotionListener[])getListeners(DragSourceMotionListener.class);
    }
    
    public EventListener[] getListeners(Class listenerType) {
        EventListener l = null;
        if (listenerType == DragSourceListener.class) {
            l = listener;
        } else if (listenerType == DragSourceMotionListener.class) {
            l = motionListener;
        }
        return DnDEventMulticaster.getListeners(l, listenerType);
    }
    
    void processDragEnter(DragSourceDragEvent dsde) {
        DragSourceListener dsl = listener;
        if (dsl != null) {
            dsl.dragEnter(dsde);
        }
    }
    
    void processDragOver(DragSourceDragEvent dsde) {
        DragSourceListener dsl = listener;
        if (dsl != null) {
            dsl.dragOver(dsde);
        }
    }
    
    void processDropActionChanged(DragSourceDragEvent dsde) {
        DragSourceListener dsl = listener;
        if (dsl != null) {
            dsl.dropActionChanged(dsde);
        }
    }
    
    void processDragExit(DragSourceEvent dse) {
        DragSourceListener dsl = listener;
        if (dsl != null) {
            dsl.dragExit(dse);
        }
    }
    
    void processDragDropEnd(DragSourceDropEvent dsde) {
        DragSourceListener dsl = listener;
        if (dsl != null) {
            dsl.dragDropEnd(dsde);
        }
    }
    
    void processDragMouseMoved(DragSourceDragEvent dsde) {
        DragSourceMotionListener dsml = motionListener;
        if (dsml != null) {
            dsml.dragMouseMoved(dsde);
        }
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        s.writeObject(SerializationTester.test(flavorMap) ? flavorMap : null);
        DnDEventMulticaster.save(s, dragSourceListenerK, listener);
        DnDEventMulticaster.save(s, dragSourceMotionListenerK, motionListener);
        s.writeObject(null);
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException {
        s.defaultReadObject();
        flavorMap = (FlavorMap)(FlavorMap)s.readObject();
        if (flavorMap == null) {
            flavorMap = SystemFlavorMap.getDefaultFlavorMap();
        }
        Object keyOrNull;
        while (null != (keyOrNull = s.readObject())) {
            String key = ((String)(String)keyOrNull).intern();
            if (dragSourceListenerK == key) {
                addDragSourceListener((DragSourceListener)((DragSourceListener)s.readObject()));
            } else if (dragSourceMotionListenerK == key) {
                addDragSourceMotionListener((DragSourceMotionListener)((DragSourceMotionListener)s.readObject()));
            } else {
                s.readObject();
            }
        }
    }
    
    public static int getDragThreshold() {
        int ts = ((Integer)(Integer)AccessController.doPrivileged(new GetIntegerAction("awt.dnd.drag.threshold", 0))).intValue();
        if (ts > 0) {
            return ts;
        } else {
            Integer td = (Integer)(Integer)Toolkit.getDefaultToolkit().getDesktopProperty("DnD.gestureMotionThreshold");
            if (td != null) {
                return td.intValue();
            }
        }
        return 5;
    }
    private transient FlavorMap flavorMap = SystemFlavorMap.getDefaultFlavorMap();
    private transient DragSourceListener listener;
    private transient DragSourceMotionListener motionListener;
}
