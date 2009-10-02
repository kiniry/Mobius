package java.awt;

import java.awt.peer.ButtonPeer;
import java.util.EventListener;
import java.awt.event.*;
import java.io.ObjectOutputStream;
import java.io.ObjectInputStream;
import java.io.IOException;
import javax.accessibility.*;

public class Button extends Component implements Accessible {
    String label;
    String actionCommand;
    transient ActionListener actionListener;
    private static final String base = "button";
    private static int nameCounter = 0;
    private static final long serialVersionUID = -8774683716313001058L;
    static {
        Toolkit.loadLibraries();
        if (!GraphicsEnvironment.isHeadless()) {
            initIDs();
        }
    }
    
    private static native void initIDs();
    
    public Button() throws HeadlessException {
        this("");
    }
    
    public Button(String label) throws HeadlessException {
        
        GraphicsEnvironment.checkHeadless();
        this.label = label;
    }
    
    String constructComponentName() {
        synchronized (getClass()) {
            return base + nameCounter++;
        }
    }
    
    public void addNotify() {
        synchronized (getTreeLock()) {
            if (peer == null) peer = getToolkit().createButton(this);
            super.addNotify();
        }
    }
    
    public String getLabel() {
        return label;
    }
    
    public void setLabel(String label) {
        boolean testvalid = false;
        synchronized (this) {
            if (label != this.label && (this.label == null || !this.label.equals(label))) {
                this.label = label;
                ButtonPeer peer = (ButtonPeer)(ButtonPeer)this.peer;
                if (peer != null) {
                    peer.setLabel(label);
                }
                testvalid = true;
            }
        }
        if (testvalid && valid) {
            invalidate();
        }
    }
    
    public void setActionCommand(String command) {
        actionCommand = command;
    }
    
    public String getActionCommand() {
        return (actionCommand == null ? label : actionCommand);
    }
    
    public synchronized void addActionListener(ActionListener l) {
        if (l == null) {
            return;
        }
        actionListener = AWTEventMulticaster.add(actionListener, l);
        newEventsOnly = true;
    }
    
    public synchronized void removeActionListener(ActionListener l) {
        if (l == null) {
            return;
        }
        actionListener = AWTEventMulticaster.remove(actionListener, l);
    }
    
    public synchronized ActionListener[] getActionListeners() {
        return (ActionListener[])((ActionListener[])getListeners(ActionListener.class));
    }
    
    public EventListener[] getListeners(Class listenerType) {
        EventListener l = null;
        if (listenerType == ActionListener.class) {
            l = actionListener;
        } else {
            return super.getListeners(listenerType);
        }
        return AWTEventMulticaster.getListeners(l, listenerType);
    }
    
    boolean eventEnabled(AWTEvent e) {
        if (e.id == ActionEvent.ACTION_PERFORMED) {
            if ((eventMask & AWTEvent.ACTION_EVENT_MASK) != 0 || actionListener != null) {
                return true;
            }
            return false;
        }
        return super.eventEnabled(e);
    }
    
    protected void processEvent(AWTEvent e) {
        if (e instanceof ActionEvent) {
            processActionEvent((ActionEvent)(ActionEvent)e);
            return;
        }
        super.processEvent(e);
    }
    
    protected void processActionEvent(ActionEvent e) {
        ActionListener listener = actionListener;
        if (listener != null) {
            listener.actionPerformed(e);
        }
    }
    
    protected String paramString() {
        return super.paramString() + ",label=" + label;
    }
    private int buttonSerializedDataVersion = 1;
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        AWTEventMulticaster.save(s, actionListenerK, actionListener);
        s.writeObject(null);
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException, HeadlessException {
        GraphicsEnvironment.checkHeadless();
        s.defaultReadObject();
        Object keyOrNull;
        while (null != (keyOrNull = s.readObject())) {
            String key = ((String)(String)keyOrNull).intern();
            if (actionListenerK == key) addActionListener((ActionListener)((ActionListener)s.readObject())); else s.readObject();
        }
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new Button$AccessibleAWTButton(this);
        }
        return accessibleContext;
    }
    {
    }
}
