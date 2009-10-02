package java.awt;

import java.awt.peer.FramePeer;
import java.awt.event.*;
import java.util.Vector;
import java.io.Serializable;
import java.io.ObjectOutputStream;
import java.io.ObjectInputStream;
import java.io.IOException;
import sun.awt.AppContext;
import sun.awt.SunToolkit;
import java.lang.ref.WeakReference;
import javax.accessibility.*;

public class Frame extends Window implements MenuContainer {
    
    public static final int DEFAULT_CURSOR = Cursor.DEFAULT_CURSOR;
    
    public static final int CROSSHAIR_CURSOR = Cursor.CROSSHAIR_CURSOR;
    
    public static final int TEXT_CURSOR = Cursor.TEXT_CURSOR;
    
    public static final int WAIT_CURSOR = Cursor.WAIT_CURSOR;
    
    public static final int SW_RESIZE_CURSOR = Cursor.SW_RESIZE_CURSOR;
    
    public static final int SE_RESIZE_CURSOR = Cursor.SE_RESIZE_CURSOR;
    
    public static final int NW_RESIZE_CURSOR = Cursor.NW_RESIZE_CURSOR;
    
    public static final int NE_RESIZE_CURSOR = Cursor.NE_RESIZE_CURSOR;
    
    public static final int N_RESIZE_CURSOR = Cursor.N_RESIZE_CURSOR;
    
    public static final int S_RESIZE_CURSOR = Cursor.S_RESIZE_CURSOR;
    
    public static final int W_RESIZE_CURSOR = Cursor.W_RESIZE_CURSOR;
    
    public static final int E_RESIZE_CURSOR = Cursor.E_RESIZE_CURSOR;
    
    public static final int HAND_CURSOR = Cursor.HAND_CURSOR;
    
    public static final int MOVE_CURSOR = Cursor.MOVE_CURSOR;
    public static final int NORMAL = 0;
    public static final int ICONIFIED = 1;
    public static final int MAXIMIZED_HORIZ = 2;
    public static final int MAXIMIZED_VERT = 4;
    public static final int MAXIMIZED_BOTH = MAXIMIZED_VERT | MAXIMIZED_HORIZ;
    Rectangle maximizedBounds;
    String title = "Untitled";
    transient Image icon;
    MenuBar menuBar;
    boolean resizable = true;
    boolean undecorated = false;
    boolean mbManagement = false;
    private int state = NORMAL;
    Vector ownedWindows;
    private transient WeakReference weakThis;
    private static final String base = "frame";
    private static int nameCounter = 0;
    private static final long serialVersionUID = 2673458971256075116L;
    static {
        Toolkit.loadLibraries();
        if (!GraphicsEnvironment.isHeadless()) {
            initIDs();
        }
    }
    
    public Frame() throws HeadlessException {
        this("");
    }
    
    public Frame(GraphicsConfiguration gc) {
        this("", gc);
    }
    
    public Frame(String title) throws HeadlessException {
        
        init(title, null);
    }
    
    public Frame(String title, GraphicsConfiguration gc) {
        super(gc);
        init(title, gc);
    }
    
    private void init(String title, GraphicsConfiguration gc) {
        this.title = title;
        weakThis = new WeakReference(this);
        addToFrameList();
        SunToolkit.checkAndSetPolicy(this, false);
    }
    
    protected void finalize() throws Throwable {
        removeFromFrameList();
        super.finalize();
    }
    
    String constructComponentName() {
        synchronized (getClass()) {
            return base + nameCounter++;
        }
    }
    
    public void addNotify() {
        synchronized (getTreeLock()) {
            if (peer == null) {
                peer = getToolkit().createFrame(this);
            }
            FramePeer p = (FramePeer)(FramePeer)peer;
            MenuBar menuBar = this.menuBar;
            if (menuBar != null) {
                mbManagement = true;
                menuBar.addNotify();
                p.setMenuBar(menuBar);
            }
            p.setMaximizedBounds(maximizedBounds);
            super.addNotify();
        }
    }
    
    public String getTitle() {
        return title;
    }
    
    public void setTitle(String title) {
        String oldTitle = this.title;
        if (title == null) {
            title = "";
        }
        synchronized (this) {
            this.title = title;
            FramePeer peer = (FramePeer)(FramePeer)this.peer;
            if (peer != null) {
                peer.setTitle(title);
            }
        }
        firePropertyChange("title", oldTitle, title);
    }
    
    public Image getIconImage() {
        return icon;
    }
    
    public synchronized void setIconImage(Image image) {
        this.icon = image;
        FramePeer peer = (FramePeer)(FramePeer)this.peer;
        if (peer != null) {
            peer.setIconImage(image);
        }
    }
    
    public MenuBar getMenuBar() {
        return menuBar;
    }
    
    public void setMenuBar(MenuBar mb) {
        synchronized (getTreeLock()) {
            if (menuBar == mb) {
                return;
            }
            if ((mb != null) && (mb.parent != null)) {
                mb.parent.remove(mb);
            }
            if (menuBar != null) {
                remove(menuBar);
            }
            menuBar = mb;
            if (menuBar != null) {
                menuBar.parent = this;
                FramePeer peer = (FramePeer)(FramePeer)this.peer;
                if (peer != null) {
                    mbManagement = true;
                    menuBar.addNotify();
                    if (valid) {
                        invalidate();
                    }
                    peer.setMenuBar(menuBar);
                }
            }
        }
    }
    
    public boolean isResizable() {
        return resizable;
    }
    
    public void setResizable(boolean resizable) {
        boolean oldResizable = this.resizable;
        boolean testvalid = false;
        synchronized (this) {
            this.resizable = resizable;
            FramePeer peer = (FramePeer)(FramePeer)this.peer;
            if (peer != null) {
                peer.setResizable(resizable);
                testvalid = true;
            }
        }
        if (testvalid && valid) {
            invalidate();
        }
        firePropertyChange("resizable", oldResizable, resizable);
    }
    
    public synchronized void setState(int state) {
        int current = getExtendedState();
        if (state == ICONIFIED && (current & ICONIFIED) == 0) {
            setExtendedState(current | ICONIFIED);
        } else if (state == NORMAL && (current & ICONIFIED) != 0) {
            setExtendedState(current & ~ICONIFIED);
        }
    }
    
    public synchronized void setExtendedState(int state) {
        if (!isFrameStateSupported(state)) {
            return;
        }
        this.state = state;
        FramePeer peer = (FramePeer)(FramePeer)this.peer;
        if (peer != null) {
            peer.setState(state);
        }
    }
    
    private boolean isFrameStateSupported(int state) {
        if (!getToolkit().isFrameStateSupported(state)) {
            if (((state & ICONIFIED) != 0) && !getToolkit().isFrameStateSupported(ICONIFIED)) {
                return false;
            } else {
                state &= ~ICONIFIED;
            }
            return getToolkit().isFrameStateSupported(state);
        }
        return true;
    }
    
    public synchronized int getState() {
        return (getExtendedState() & ICONIFIED) != 0 ? ICONIFIED : NORMAL;
    }
    
    public synchronized int getExtendedState() {
        FramePeer peer = (FramePeer)(FramePeer)this.peer;
        if (peer != null) {
            state = peer.getState();
        }
        return state;
    }
    
    public synchronized void setMaximizedBounds(Rectangle bounds) {
        this.maximizedBounds = bounds;
        FramePeer peer = (FramePeer)(FramePeer)this.peer;
        if (peer != null) {
            peer.setMaximizedBounds(bounds);
        }
    }
    
    public Rectangle getMaximizedBounds() {
        return maximizedBounds;
    }
    
    public void setUndecorated(boolean undecorated) {
        synchronized (getTreeLock()) {
            if (isDisplayable()) {
                throw new IllegalComponentStateException("The frame is displayable.");
            }
            this.undecorated = undecorated;
        }
    }
    
    public boolean isUndecorated() {
        return undecorated;
    }
    
    public void remove(MenuComponent m) {
        synchronized (getTreeLock()) {
            if (m == menuBar) {
                menuBar = null;
                FramePeer peer = (FramePeer)(FramePeer)this.peer;
                if (peer != null) {
                    mbManagement = true;
                    if (valid) {
                        invalidate();
                    }
                    peer.setMenuBar(null);
                    m.removeNotify();
                }
                m.parent = null;
            } else {
                super.remove(m);
            }
        }
    }
    
    public void removeNotify() {
        synchronized (getTreeLock()) {
            FramePeer peer = (FramePeer)(FramePeer)this.peer;
            if (peer != null) {
                getState();
                if (menuBar != null) {
                    mbManagement = true;
                    peer.setMenuBar(null);
                    menuBar.removeNotify();
                }
            }
            super.removeNotify();
        }
    }
    
    void postProcessKeyEvent(KeyEvent e) {
        if (menuBar != null && menuBar.handleShortcut(e)) {
            e.consume();
            return;
        }
        super.postProcessKeyEvent(e);
    }
    
    protected String paramString() {
        String str = super.paramString();
        if (title != null) {
            str += ",title=" + title;
        }
        if (resizable) {
            str += ",resizable";
        }
        getExtendedState();
        if (state == NORMAL) {
            str += ",normal";
        } else {
            if ((state & ICONIFIED) != 0) {
                str += ",iconified";
            }
            if ((state & MAXIMIZED_BOTH) == MAXIMIZED_BOTH) {
                str += ",maximized";
            } else if ((state & MAXIMIZED_HORIZ) != 0) {
                str += ",maximized_horiz";
            } else if ((state & MAXIMIZED_VERT) != 0) {
                str += ",maximized_vert";
            }
        }
        return str;
    }
    
    
    public void setCursor(int cursorType) {
        if (cursorType < DEFAULT_CURSOR || cursorType > MOVE_CURSOR) {
            throw new IllegalArgumentException("illegal cursor type");
        }
        setCursor(Cursor.getPredefinedCursor(cursorType));
    }
    
    
    public int getCursorType() {
        return (getCursor().getType());
    }
    
    public static Frame[] getFrames() {
        synchronized (Frame.class) {
            Frame[] realCopy;
            Vector frameList = (Vector)(Vector)AppContext.getAppContext().get(Frame.class);
            if (frameList != null) {
                int fullSize = frameList.size();
                int realSize = 0;
                Frame[] fullCopy = new Frame[fullSize];
                for (int i = 0; i < fullSize; i++) {
                    fullCopy[realSize] = (Frame)((Frame)((WeakReference)((WeakReference)frameList.elementAt(i))).get());
                    if (fullCopy[realSize] != null) {
                        realSize++;
                    }
                }
                if (fullSize != realSize) {
                    realCopy = new Frame[realSize];
                    System.arraycopy(fullCopy, 0, realCopy, 0, realSize);
                } else {
                    realCopy = fullCopy;
                }
            } else {
                realCopy = new Frame[0];
            }
            return realCopy;
        }
    }
    
    void addToFrameList() {
        synchronized (Frame.class) {
            Vector frameList = (Vector)(Vector)appContext.get(Frame.class);
            if (frameList == null) {
                frameList = new Vector();
                appContext.put(Frame.class, frameList);
            }
            frameList.addElement(weakThis);
        }
    }
    
    void removeFromFrameList() {
        synchronized (Frame.class) {
            Vector frameList = (Vector)(Vector)appContext.get(Frame.class);
            if (frameList != null) {
                frameList.removeElement(weakThis);
            }
        }
    }
    private int frameSerializedDataVersion = 1;
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        if (icon instanceof Serializable) {
            s.writeObject(icon);
        } else {
            s.writeObject(null);
        }
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException, HeadlessException {
        s.defaultReadObject();
        try {
            icon = (Image)(Image)s.readObject();
        } catch (java.io.OptionalDataException e) {
            if (!e.eof) {
                throw (e);
            }
        }
        if (menuBar != null) menuBar.parent = this;
        if (ownedWindows != null) {
            for (int i = 0; i < ownedWindows.size(); i++) {
                connectOwnedWindow((Window)(Window)ownedWindows.elementAt(i));
            }
            ownedWindows = null;
        }
        weakThis = new WeakReference(this);
        addToFrameList();
    }
    
    private static native void initIDs();
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new Frame$AccessibleAWTFrame(this);
        }
        return accessibleContext;
    }
    {
    }
}
