package java.awt;

import java.awt.peer.DialogPeer;
import java.awt.event.*;
import javax.accessibility.*;
import sun.awt.AppContext;
import sun.awt.SunToolkit;
import sun.awt.PeerEvent;
import java.security.AccessController;
import java.util.concurrent.atomic.AtomicLong;

public class Dialog extends Window {
    
    /*synthetic*/ static boolean access$000(Dialog x0) {
        return x0.keepBlocking;
    }
    static {
        Toolkit.loadLibraries();
        if (!GraphicsEnvironment.isHeadless()) {
            initIDs();
        }
    }
    boolean resizable = true;
    boolean undecorated = false;
    boolean modal;
    String title;
    private transient boolean keepBlocking = false;
    private static final String base = "dialog";
    private static int nameCounter = 0;
    private static final long serialVersionUID = 5920926903803293709L;
    
    public Dialog(Frame owner) {
        this(owner, "", false);
    }
    
    public Dialog(Frame owner, boolean modal) {
        this(owner, "", modal);
    }
    
    public Dialog(Frame owner, String title) {
        this(owner, title, false);
    }
    
    public Dialog(Frame owner, String title, boolean modal) {
        super(owner);
        this.title = title;
        this.modal = modal;
        SunToolkit.checkAndSetPolicy(this, false);
    }
    
    public Dialog(Frame owner, String title, boolean modal, GraphicsConfiguration gc) {
        super(owner, gc);
        this.title = title;
        this.modal = modal;
        SunToolkit.checkAndSetPolicy(this, false);
    }
    
    public Dialog(Dialog owner) {
        this(owner, "", false);
    }
    
    public Dialog(Dialog owner, String title) {
        this(owner, title, false);
    }
    
    public Dialog(Dialog owner, String title, boolean modal) {
        super(owner);
        this.title = title;
        this.modal = modal;
        SunToolkit.checkAndSetPolicy(this, false);
    }
    
    public Dialog(Dialog owner, String title, boolean modal, GraphicsConfiguration gc) {
        super(owner, gc);
        this.title = title;
        this.modal = modal;
        SunToolkit.checkAndSetPolicy(this, false);
    }
    
    String constructComponentName() {
        synchronized (getClass()) {
            return base + nameCounter++;
        }
    }
    
    public void addNotify() {
        synchronized (getTreeLock()) {
            if (parent != null && parent.getPeer() == null) {
                parent.addNotify();
            }
            if (peer == null) {
                peer = getToolkit().createDialog(this);
            }
            super.addNotify();
        }
    }
    
    public boolean isModal() {
        return modal;
    }
    
    public void setModal(boolean b) {
        this.modal = b;
    }
    
    public String getTitle() {
        return title;
    }
    
    public void setTitle(String title) {
        String oldTitle = this.title;
        synchronized (this) {
            this.title = title;
            DialogPeer peer = (DialogPeer)(DialogPeer)this.peer;
            if (peer != null) {
                peer.setTitle(title);
            }
        }
        firePropertyChange("title", oldTitle, title);
    }
    
    private boolean conditionalShow(Component toFocus, AtomicLong time) {
        boolean retval;
        synchronized (getTreeLock()) {
            if (peer == null) {
                addNotify();
            }
            validate();
            if (visible) {
                toFront();
                retval = false;
            } else {
                visible = retval = true;
                if (toFocus != null && time != null && isFocusable() && isEnabled()) {
                    time.set(Toolkit.getEventQueue().getMostRecentEventTimeEx());
                    KeyboardFocusManager.getCurrentKeyboardFocusManager().enqueueKeyEvents(time.get(), toFocus);
                }
                peer.show();
                for (int i = 0; i < ownedWindowList.size(); i++) {
                    Window child = (Window)((.java.lang.ref.WeakReference)ownedWindowList.elementAt(i)).get();
                    if ((child != null) && child.showWithParent) {
                        child.show();
                        child.showWithParent = false;
                    }
                }
                Window.updateChildFocusableWindowState(this);
                createHierarchyEvents(HierarchyEvent.HIERARCHY_CHANGED, this, parent, HierarchyEvent.SHOWING_CHANGED, Toolkit.enabledOnToolkit(AWTEvent.HIERARCHY_EVENT_MASK));
            }
            if (retval && (componentListener != null || (eventMask & AWTEvent.COMPONENT_EVENT_MASK) != 0 || Toolkit.enabledOnToolkit(AWTEvent.COMPONENT_EVENT_MASK))) {
                ComponentEvent e = new ComponentEvent(this, ComponentEvent.COMPONENT_SHOWN);
                Toolkit.getEventQueue().postEvent(e);
            }
        }
        if (retval && (state & OPENED) == 0) {
            postWindowEvent(WindowEvent.WINDOW_OPENED);
            state |= OPENED;
        }
        return retval;
    }
    private transient AppContext showAppContext;
    
    
    public void show() {
        beforeFirstShow = false;
        if (!isModal()) {
            conditionalShow(null, null);
        } else {
            keepBlocking = true;
            showAppContext = AppContext.getAppContext();
            AtomicLong time = new AtomicLong();
            Component predictedFocusOwner = getMostRecentFocusOwner();
            try {
                if (conditionalShow(predictedFocusOwner, time)) {
                    final Runnable pumpEventsForHierarchy = new Dialog$1(this);
                    modalityPushed();
                    try {
                        if (EventQueue.isDispatchThread()) {
                            SequencedEvent currentSequencedEvent = KeyboardFocusManager.getCurrentKeyboardFocusManager().getCurrentSequencedEvent();
                            if (currentSequencedEvent != null) {
                                currentSequencedEvent.dispose();
                            }
                            AccessController.doPrivileged(new Dialog$2(this, pumpEventsForHierarchy));
                        } else {
                            synchronized (getTreeLock()) {
                                Toolkit.getEventQueue().postEvent(new PeerEvent(this, pumpEventsForHierarchy, PeerEvent.PRIORITY_EVENT));
                                while (keepBlocking && windowClosingException == null) {
                                    try {
                                        getTreeLock().wait();
                                    } catch (InterruptedException e) {
                                        break;
                                    }
                                }
                            }
                        }
                    } finally {
                        modalityPopped();
                    }
                    if (windowClosingException != null) {
                        windowClosingException.fillInStackTrace();
                        throw windowClosingException;
                    }
                }
            } finally {
                KeyboardFocusManager.getCurrentKeyboardFocusManager().dequeueKeyEvents(time.get(), predictedFocusOwner);
            }
        }
    }
    
    final void modalityPushed() {
        Toolkit tk = Toolkit.getDefaultToolkit();
        if (tk instanceof SunToolkit) {
            SunToolkit stk = (SunToolkit)(SunToolkit)tk;
            stk.notifyModalityPushed(this);
        }
    }
    
    final void modalityPopped() {
        Toolkit tk = Toolkit.getDefaultToolkit();
        if (tk instanceof SunToolkit) {
            SunToolkit stk = (SunToolkit)(SunToolkit)tk;
            stk.notifyModalityPopped(this);
        }
    }
    
    void interruptBlocking() {
        if (modal) {
            disposeImpl();
        } else if (windowClosingException != null) {
            windowClosingException.fillInStackTrace();
            windowClosingException.printStackTrace();
            windowClosingException = null;
        }
    }
    {
    }
    
    private void hideAndDisposeHandler() {
        if (keepBlocking) {
            synchronized (getTreeLock()) {
                keepBlocking = false;
                if (showAppContext != null) {
                    SunToolkit.postEvent(showAppContext, new PeerEvent(this, new Dialog$WakingRunnable(), PeerEvent.PRIORITY_EVENT));
                    showAppContext = null;
                }
                EventQueue.invokeLater(new Dialog$WakingRunnable());
                getTreeLock().notifyAll();
            }
        }
    }
    
    
    public void hide() {
        super.hide();
        hideAndDisposeHandler();
    }
    
    void doDispose() {
        super.doDispose();
        hideAndDisposeHandler();
    }
    
    public boolean isResizable() {
        return resizable;
    }
    
    public void setResizable(boolean resizable) {
        boolean testvalid = false;
        synchronized (this) {
            this.resizable = resizable;
            DialogPeer peer = (DialogPeer)(DialogPeer)this.peer;
            if (peer != null) {
                peer.setResizable(resizable);
                testvalid = true;
            }
        }
        if (testvalid && valid) {
            invalidate();
        }
    }
    
    public void setUndecorated(boolean undecorated) {
        synchronized (getTreeLock()) {
            if (isDisplayable()) {
                throw new IllegalComponentStateException("The dialog is displayable.");
            }
            this.undecorated = undecorated;
        }
    }
    
    public boolean isUndecorated() {
        return undecorated;
    }
    
    protected String paramString() {
        String str = super.paramString() + (modal ? ",modal" : ",modeless");
        if (title != null) {
            str += ",title=" + title;
        }
        return str;
    }
    
    private static native void initIDs();
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new Dialog$AccessibleAWTDialog(this);
        }
        return accessibleContext;
    }
    {
    }
}
