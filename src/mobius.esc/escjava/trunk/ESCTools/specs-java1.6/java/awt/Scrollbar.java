package java.awt;

import java.awt.peer.ScrollbarPeer;
import java.awt.event.*;
import java.util.EventListener;
import java.io.ObjectOutputStream;
import java.io.ObjectInputStream;
import java.io.IOException;
import javax.accessibility.*;

public class Scrollbar extends Component implements Adjustable, Accessible {
    public static final int HORIZONTAL = 0;
    public static final int VERTICAL = 1;
    int value;
    int maximum;
    int minimum;
    int visibleAmount;
    int orientation;
    int lineIncrement = 1;
    int pageIncrement = 10;
    transient boolean isAdjusting;
    transient AdjustmentListener adjustmentListener;
    private static final String base = "scrollbar";
    private static int nameCounter = 0;
    private static final long serialVersionUID = 8451667562882310543L;
    
    private static native void initIDs();
    static {
        Toolkit.loadLibraries();
        if (!GraphicsEnvironment.isHeadless()) {
            initIDs();
        }
    }
    
    public Scrollbar() throws HeadlessException {
        this(VERTICAL, 0, 10, 0, 100);
    }
    
    public Scrollbar(int orientation) throws HeadlessException {
        this(orientation, 0, 10, 0, 100);
    }
    
    public Scrollbar(int orientation, int value, int visible, int minimum, int maximum) throws HeadlessException {
        
        GraphicsEnvironment.checkHeadless();
        switch (orientation) {
        case HORIZONTAL: 
        
        case VERTICAL: 
            this.orientation = orientation;
            break;
        
        default: 
            throw new IllegalArgumentException("illegal scrollbar orientation");
        
        }
        setValues(value, visible, minimum, maximum);
    }
    
    String constructComponentName() {
        synchronized (getClass()) {
            return base + nameCounter++;
        }
    }
    
    public void addNotify() {
        synchronized (getTreeLock()) {
            if (peer == null) peer = getToolkit().createScrollbar(this);
            super.addNotify();
        }
    }
    
    public int getOrientation() {
        return orientation;
    }
    
    public void setOrientation(int orientation) {
        synchronized (getTreeLock()) {
            if (orientation == this.orientation) {
                return;
            }
            switch (orientation) {
            case HORIZONTAL: 
            
            case VERTICAL: 
                this.orientation = orientation;
                break;
            
            default: 
                throw new IllegalArgumentException("illegal scrollbar orientation");
            
            }
            if (peer != null) {
                removeNotify();
                addNotify();
                invalidate();
            }
        }
        if (accessibleContext != null) {
            accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, ((orientation == VERTICAL) ? AccessibleState.HORIZONTAL : AccessibleState.VERTICAL), ((orientation == VERTICAL) ? AccessibleState.VERTICAL : AccessibleState.HORIZONTAL));
        }
    }
    
    public int getValue() {
        return value;
    }
    
    public void setValue(int newValue) {
        setValues(newValue, visibleAmount, minimum, maximum);
    }
    
    public int getMinimum() {
        return minimum;
    }
    
    public void setMinimum(int newMinimum) {
        setValues(value, visibleAmount, newMinimum, maximum);
    }
    
    public int getMaximum() {
        return maximum;
    }
    
    public void setMaximum(int newMaximum) {
        if (newMaximum == Integer.MIN_VALUE) {
            newMaximum = Integer.MIN_VALUE + 1;
        }
        if (minimum >= newMaximum) {
            minimum = newMaximum - 1;
        }
        setValues(value, visibleAmount, minimum, newMaximum);
    }
    
    public int getVisibleAmount() {
        return getVisible();
    }
    
    
    public int getVisible() {
        return visibleAmount;
    }
    
    public void setVisibleAmount(int newAmount) {
        setValues(value, newAmount, minimum, maximum);
    }
    
    public void setUnitIncrement(int v) {
        setLineIncrement(v);
    }
    
    
    public synchronized void setLineIncrement(int v) {
        int tmp = (v < 1) ? 1 : v;
        if (lineIncrement == tmp) {
            return;
        }
        lineIncrement = tmp;
        ScrollbarPeer peer = (ScrollbarPeer)(ScrollbarPeer)this.peer;
        if (peer != null) {
            peer.setLineIncrement(lineIncrement);
        }
    }
    
    public int getUnitIncrement() {
        return getLineIncrement();
    }
    
    
    public int getLineIncrement() {
        return lineIncrement;
    }
    
    public void setBlockIncrement(int v) {
        setPageIncrement(v);
    }
    
    
    public synchronized void setPageIncrement(int v) {
        int tmp = (v < 1) ? 1 : v;
        if (pageIncrement == tmp) {
            return;
        }
        pageIncrement = tmp;
        ScrollbarPeer peer = (ScrollbarPeer)(ScrollbarPeer)this.peer;
        if (peer != null) {
            peer.setPageIncrement(pageIncrement);
        }
    }
    
    public int getBlockIncrement() {
        return getPageIncrement();
    }
    
    
    public int getPageIncrement() {
        return pageIncrement;
    }
    
    public void setValues(int value, int visible, int minimum, int maximum) {
        int oldValue;
        synchronized (this) {
            if (minimum == Integer.MAX_VALUE) {
                minimum = Integer.MAX_VALUE - 1;
            }
            if (maximum <= minimum) {
                maximum = minimum + 1;
            }
            long maxMinusMin = (long)maximum - (long)minimum;
            if (maxMinusMin > Integer.MAX_VALUE) {
                maxMinusMin = Integer.MAX_VALUE;
                maximum = minimum + (int)maxMinusMin;
            }
            if (visible > (int)maxMinusMin) {
                visible = (int)maxMinusMin;
            }
            if (visible < 1) {
                visible = 1;
            }
            if (value < minimum) {
                value = minimum;
            }
            if (value > maximum - visible) {
                value = maximum - visible;
            }
            oldValue = this.value;
            this.value = value;
            this.visibleAmount = visible;
            this.minimum = minimum;
            this.maximum = maximum;
            ScrollbarPeer peer = (ScrollbarPeer)(ScrollbarPeer)this.peer;
            if (peer != null) {
                peer.setValues(value, visibleAmount, minimum, maximum);
            }
        }
        if ((oldValue != value) && (accessibleContext != null)) {
            accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_VALUE_PROPERTY, new Integer(oldValue), new Integer(value));
        }
    }
    
    public boolean getValueIsAdjusting() {
        return isAdjusting;
    }
    
    public void setValueIsAdjusting(boolean b) {
        boolean oldValue;
        synchronized (this) {
            oldValue = isAdjusting;
            isAdjusting = b;
        }
        if ((oldValue != b) && (accessibleContext != null)) {
            accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, ((oldValue) ? AccessibleState.BUSY : null), ((b) ? AccessibleState.BUSY : null));
        }
    }
    
    public synchronized void addAdjustmentListener(AdjustmentListener l) {
        if (l == null) {
            return;
        }
        adjustmentListener = AWTEventMulticaster.add(adjustmentListener, l);
        newEventsOnly = true;
    }
    
    public synchronized void removeAdjustmentListener(AdjustmentListener l) {
        if (l == null) {
            return;
        }
        adjustmentListener = AWTEventMulticaster.remove(adjustmentListener, l);
    }
    
    public synchronized AdjustmentListener[] getAdjustmentListeners() {
        return (AdjustmentListener[])((AdjustmentListener[])getListeners(AdjustmentListener.class));
    }
    
    public EventListener[] getListeners(Class listenerType) {
        EventListener l = null;
        if (listenerType == AdjustmentListener.class) {
            l = adjustmentListener;
        } else {
            return super.getListeners(listenerType);
        }
        return AWTEventMulticaster.getListeners(l, listenerType);
    }
    
    boolean eventEnabled(AWTEvent e) {
        if (e.id == AdjustmentEvent.ADJUSTMENT_VALUE_CHANGED) {
            if ((eventMask & AWTEvent.ADJUSTMENT_EVENT_MASK) != 0 || adjustmentListener != null) {
                return true;
            }
            return false;
        }
        return super.eventEnabled(e);
    }
    
    protected void processEvent(AWTEvent e) {
        if (e instanceof AdjustmentEvent) {
            processAdjustmentEvent((AdjustmentEvent)(AdjustmentEvent)e);
            return;
        }
        super.processEvent(e);
    }
    
    protected void processAdjustmentEvent(AdjustmentEvent e) {
        AdjustmentListener listener = adjustmentListener;
        if (listener != null) {
            listener.adjustmentValueChanged(e);
        }
    }
    
    protected String paramString() {
        return super.paramString() + ",val=" + value + ",vis=" + visibleAmount + ",min=" + minimum + ",max=" + maximum + ((orientation == VERTICAL) ? ",vert" : ",horz") + ",isAdjusting=" + isAdjusting;
    }
    private int scrollbarSerializedDataVersion = 1;
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        AWTEventMulticaster.save(s, adjustmentListenerK, adjustmentListener);
        s.writeObject(null);
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException, HeadlessException {
        GraphicsEnvironment.checkHeadless();
        s.defaultReadObject();
        Object keyOrNull;
        while (null != (keyOrNull = s.readObject())) {
            String key = ((String)(String)keyOrNull).intern();
            if (adjustmentListenerK == key) addAdjustmentListener((AdjustmentListener)((AdjustmentListener)s.readObject())); else s.readObject();
        }
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new Scrollbar$AccessibleAWTScrollBar(this);
        }
        return accessibleContext;
    }
    {
    }
}
