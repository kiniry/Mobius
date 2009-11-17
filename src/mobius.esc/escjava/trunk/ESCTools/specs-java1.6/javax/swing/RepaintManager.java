package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.awt.peer.ComponentPeer;
import java.awt.peer.ContainerPeer;
import java.awt.image.VolatileImage;
import java.util.*;
import java.applet.*;
import sun.security.action.GetPropertyAction;

public class RepaintManager {
    {
    }
    private Map volatileMap = new HashMap(1);
    Hashtable dirtyComponents = new Hashtable();
    Hashtable tmpDirtyComponents = new Hashtable();
    Vector invalidComponents;
    boolean doubleBufferingEnabled = true;
    private Dimension doubleBufferMaxSize;
    RepaintManager$DoubleBufferInfo standardDoubleBuffer;
    private static final Object repaintManagerKey = RepaintManager.class;
    static boolean volatileImageBufferEnabled = true;
    static final int VOLATILE_LOOP_MAX = 2;
    static {
        String vib = (String)(String)java.security.AccessController.doPrivileged(new GetPropertyAction("swing.volatileImageBufferEnabled"));
        volatileImageBufferEnabled = (vib == null || vib.equals("true"));
    }
    
    public static RepaintManager currentManager(Component c) {
        RepaintManager result = (RepaintManager)(RepaintManager)SwingUtilities.appContextGet(repaintManagerKey);
        if (result == null) {
            result = new RepaintManager();
            SwingUtilities.appContextPut(repaintManagerKey, result);
        }
        return result;
    }
    
    public static RepaintManager currentManager(JComponent c) {
        return currentManager((Component)c);
    }
    
    public static void setCurrentManager(RepaintManager aRepaintManager) {
        if (aRepaintManager != null) {
            SwingUtilities.appContextPut(repaintManagerKey, aRepaintManager);
        } else {
            SwingUtilities.appContextRemove(repaintManagerKey);
        }
    }
    
    public RepaintManager() {
        
        Object dbe = java.security.AccessController.doPrivileged(new GetPropertyAction("awt.nativeDoubleBuffering"));
        boolean nativeDoubleBuffering = (dbe != null) ? Boolean.valueOf(dbe.toString()).booleanValue() : false;
        doubleBufferingEnabled = !nativeDoubleBuffering;
    }
    
    public synchronized void addInvalidComponent(JComponent invalidComponent) {
        Component validateRoot = null;
        for (Component c = invalidComponent; c != null; c = c.getParent()) {
            if ((c instanceof CellRendererPane) || (c.getPeer() == null)) {
                return;
            }
            if ((c instanceof JComponent) && (((JComponent)(JComponent)c).isValidateRoot())) {
                validateRoot = c;
                break;
            }
        }
        if (validateRoot == null) {
            return;
        }
        Component root = null;
        for (Component c = validateRoot; c != null; c = c.getParent()) {
            if (!c.isVisible() || (c.getPeer() == null)) {
                return;
            }
            if ((c instanceof Window) || (c instanceof Applet)) {
                root = c;
                break;
            }
        }
        if (root == null) {
            return;
        }
        if (invalidComponents == null) {
            invalidComponents = new Vector();
        } else {
            int n = invalidComponents.size();
            for (int i = 0; i < n; i++) {
                if (validateRoot == (Component)((Component)invalidComponents.elementAt(i))) {
                    return;
                }
            }
        }
        invalidComponents.addElement(validateRoot);
        SystemEventQueueUtilities.queueComponentWorkRequest(root);
    }
    
    public synchronized void removeInvalidComponent(JComponent component) {
        if (invalidComponents != null) {
            int index = invalidComponents.indexOf(component);
            if (index != -1) {
                invalidComponents.removeElementAt(index);
            }
        }
    }
    
    public void addDirtyRegion(JComponent c, int x, int y, int w, int h) {
        if ((w <= 0) || (h <= 0) || (c == null)) {
            return;
        }
        if ((c.getWidth() <= 0) || (c.getHeight() <= 0)) {
            return;
        }
        if (extendDirtyRegion(c, x, y, w, h)) {
            return;
        }
        Component root = null;
        for (Container p = c; p != null; p = p.getParent()) {
            if (!p.isVisible() || (p.getPeer() == null)) {
                return;
            }
            if ((p instanceof Window) || (p instanceof Applet)) {
                if (p instanceof Frame && (((Frame)(Frame)p).getExtendedState() & Frame.ICONIFIED) == Frame.ICONIFIED) {
                    return;
                }
                root = p;
                break;
            }
        }
        if (root == null) return;
        synchronized (this) {
            if (extendDirtyRegion(c, x, y, w, h)) {
                return;
            }
            dirtyComponents.put(c, new Rectangle(x, y, w, h));
        }
        SystemEventQueueUtilities.queueComponentWorkRequest(root);
    }
    
    private synchronized boolean extendDirtyRegion(Component c, int x, int y, int w, int h) {
        Rectangle r = (Rectangle)(Rectangle)dirtyComponents.get(c);
        if (r != null) {
            SwingUtilities.computeUnion(x, y, w, h, r);
            return true;
        }
        return false;
    }
    
    public Rectangle getDirtyRegion(JComponent aComponent) {
        Rectangle r = null;
        synchronized (this) {
            r = (Rectangle)(Rectangle)dirtyComponents.get(aComponent);
        }
        if (r == null) return new Rectangle(0, 0, 0, 0); else return new Rectangle(r);
    }
    
    public void markCompletelyDirty(JComponent aComponent) {
        addDirtyRegion(aComponent, 0, 0, Integer.MAX_VALUE, Integer.MAX_VALUE);
    }
    
    public void markCompletelyClean(JComponent aComponent) {
        synchronized (this) {
            dirtyComponents.remove(aComponent);
        }
    }
    
    public boolean isCompletelyDirty(JComponent aComponent) {
        Rectangle r;
        r = getDirtyRegion(aComponent);
        if (r.width == Integer.MAX_VALUE && r.height == Integer.MAX_VALUE) return true; else return false;
    }
    
    public void validateInvalidComponents() {
        Vector ic;
        synchronized (this) {
            if (invalidComponents == null) {
                return;
            }
            ic = invalidComponents;
            invalidComponents = null;
        }
        int n = ic.size();
        for (int i = 0; i < n; i++) {
            ((Component)(Component)ic.elementAt(i)).validate();
        }
    }
    
    public void paintDirtyRegions() {
        int i;
        int count;
        Vector roots;
        JComponent dirtyComponent;
        synchronized (this) {
            Hashtable tmp = tmpDirtyComponents;
            tmpDirtyComponents = dirtyComponents;
            dirtyComponents = tmp;
            dirtyComponents.clear();
        }
        count = tmpDirtyComponents.size();
        if (count == 0) {
            return;
        }
        Rectangle rect;
        int localBoundsX = 0;
        int localBoundsY = 0;
        int localBoundsH = 0;
        int localBoundsW = 0;
        Enumeration keys;
        roots = new Vector(count);
        keys = tmpDirtyComponents.keys();
        while (keys.hasMoreElements()) {
            dirtyComponent = (JComponent)(JComponent)keys.nextElement();
            collectDirtyComponents(tmpDirtyComponents, dirtyComponent, roots);
        }
        count = roots.size();
        for (i = 0; i < count; i++) {
            dirtyComponent = (JComponent)(JComponent)roots.elementAt(i);
            rect = (Rectangle)(Rectangle)tmpDirtyComponents.get(dirtyComponent);
            localBoundsH = dirtyComponent.getHeight();
            localBoundsW = dirtyComponent.getWidth();
            SwingUtilities.computeIntersection(localBoundsX, localBoundsY, localBoundsW, localBoundsH, rect);
            if (rect.x == 0 && rect.y == 0 && rect.width == dirtyComponent.getWidth() && rect.height == dirtyComponent.getHeight()) {
                Container parent = dirtyComponent.getParent();
                ComponentPeer parentPeer;
                if (parent != null && !parent.isLightweight() && (parentPeer = parent.getPeer()) != null) {
                    ((ContainerPeer)(ContainerPeer)parentPeer).cancelPendingPaint(dirtyComponent.getX(), dirtyComponent.getY(), rect.width, rect.height);
                }
            }
            dirtyComponent.paintImmediately(rect.x, rect.y, rect.width, rect.height);
        }
        tmpDirtyComponents.clear();
    }
    Rectangle tmp = new Rectangle();
    
    void collectDirtyComponents(Hashtable dirtyComponents, JComponent dirtyComponent, Vector roots) {
        int dx;
        int dy;
        int rootDx;
        int rootDy;
        Component component;
        Component rootDirtyComponent;
        Component parent;
        Rectangle cBounds;
        component = rootDirtyComponent = dirtyComponent;
        int x = dirtyComponent.getX();
        int y = dirtyComponent.getY();
        int w = dirtyComponent.getWidth();
        int h = dirtyComponent.getHeight();
        dx = rootDx = 0;
        dy = rootDy = 0;
        tmp.setBounds((Rectangle)(Rectangle)dirtyComponents.get(dirtyComponent));
        SwingUtilities.computeIntersection(0, 0, w, h, tmp);
        if (tmp.isEmpty()) {
            return;
        }
        for (; ; ) {
            parent = component.getParent();
            if (parent == null) break;
            if (!(parent instanceof JComponent)) break;
            component = parent;
            dx += x;
            dy += y;
            tmp.setLocation(tmp.x + x, tmp.y + y);
            x = component.getX();
            y = component.getY();
            w = component.getWidth();
            h = component.getHeight();
            tmp = SwingUtilities.computeIntersection(0, 0, w, h, tmp);
            if (tmp.isEmpty()) {
                return;
            }
            if (dirtyComponents.get(component) != null) {
                rootDirtyComponent = component;
                rootDx = dx;
                rootDy = dy;
            }
        }
        if (dirtyComponent != rootDirtyComponent) {
            Rectangle r;
            tmp.setLocation(tmp.x + rootDx - dx, tmp.y + rootDy - dy);
            r = (Rectangle)(Rectangle)dirtyComponents.get(rootDirtyComponent);
            SwingUtilities.computeUnion(tmp.x, tmp.y, tmp.width, tmp.height, r);
        }
        if (!roots.contains(rootDirtyComponent)) roots.addElement(rootDirtyComponent);
    }
    
    public synchronized String toString() {
        StringBuffer sb = new StringBuffer();
        if (dirtyComponents != null) sb.append("" + dirtyComponents);
        return sb.toString();
    }
    
    public Image getOffscreenBuffer(Component c, int proposedWidth, int proposedHeight) {
        return _getOffscreenBuffer(c, proposedWidth, proposedHeight);
    }
    
    public Image getVolatileOffscreenBuffer(Component c, int proposedWidth, int proposedHeight) {
        GraphicsConfiguration config = c.getGraphicsConfiguration();
        if (config == null) {
            config = GraphicsEnvironment.getLocalGraphicsEnvironment().getDefaultScreenDevice().getDefaultConfiguration();
        }
        Dimension maxSize = getDoubleBufferMaximumSize();
        int width = proposedWidth < 1 ? 1 : (proposedWidth > maxSize.width ? maxSize.width : proposedWidth);
        int height = proposedHeight < 1 ? 1 : (proposedHeight > maxSize.height ? maxSize.height : proposedHeight);
        VolatileImage image = (VolatileImage)(VolatileImage)volatileMap.get(config);
        if (image == null || image.getWidth() < width || image.getHeight() < height) {
            if (image != null) {
                image.flush();
            }
            image = config.createCompatibleVolatileImage(width, height);
            volatileMap.put(config, image);
        }
        return image;
    }
    
    private Image _getOffscreenBuffer(Component c, int proposedWidth, int proposedHeight) {
        Dimension maxSize = getDoubleBufferMaximumSize();
        RepaintManager$DoubleBufferInfo doubleBuffer = null;
        int width;
        int height;
        if (standardDoubleBuffer == null) {
            standardDoubleBuffer = new RepaintManager$DoubleBufferInfo(this, null);
        }
        doubleBuffer = standardDoubleBuffer;
        width = proposedWidth < 1 ? 1 : (proposedWidth > maxSize.width ? maxSize.width : proposedWidth);
        height = proposedHeight < 1 ? 1 : (proposedHeight > maxSize.height ? maxSize.height : proposedHeight);
        if (doubleBuffer.needsReset || (doubleBuffer.image != null && (doubleBuffer.size.width < width || doubleBuffer.size.height < height))) {
            doubleBuffer.needsReset = false;
            if (doubleBuffer.image != null) {
                doubleBuffer.image.flush();
                doubleBuffer.image = null;
            }
            width = Math.max(doubleBuffer.size.width, width);
            height = Math.max(doubleBuffer.size.height, height);
        }
        Image result = doubleBuffer.image;
        if (doubleBuffer.image == null) {
            result = c.createImage(width, height);
            doubleBuffer.size = new Dimension(width, height);
            if (c instanceof JComponent) {
                ((JComponent)(JComponent)c).setCreatedDoubleBuffer(true);
                doubleBuffer.image = result;
            }
        }
        return result;
    }
    
    public void setDoubleBufferMaximumSize(Dimension d) {
        doubleBufferMaxSize = d;
        if (standardDoubleBuffer != null && standardDoubleBuffer.image != null) {
            if (standardDoubleBuffer.image.getWidth(null) > d.width || standardDoubleBuffer.image.getHeight(null) > d.height) {
                standardDoubleBuffer.image = null;
            }
        }
        Iterator gcs = volatileMap.keySet().iterator();
        while (gcs.hasNext()) {
            GraphicsConfiguration gc = (GraphicsConfiguration)(GraphicsConfiguration)gcs.next();
            VolatileImage image = (VolatileImage)(VolatileImage)volatileMap.get(gc);
            if (image.getWidth() > d.width || image.getHeight() > d.height) {
                image.flush();
                gcs.remove();
            }
        }
    }
    
    public Dimension getDoubleBufferMaximumSize() {
        if (doubleBufferMaxSize == null) {
            try {
                Rectangle virtualBounds = new Rectangle();
                GraphicsEnvironment ge = GraphicsEnvironment.getLocalGraphicsEnvironment();
                for (GraphicsDevice[] arr$ = ge.getScreenDevices(), len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
                    GraphicsDevice gd = arr$[i$];
                    {
                        GraphicsConfiguration gc = gd.getDefaultConfiguration();
                        virtualBounds = virtualBounds.union(gc.getBounds());
                    }
                }
                doubleBufferMaxSize = new Dimension(virtualBounds.width, virtualBounds.height);
            } catch (HeadlessException e) {
                doubleBufferMaxSize = new Dimension(Integer.MAX_VALUE, Integer.MAX_VALUE);
            }
        }
        return doubleBufferMaxSize;
    }
    
    public void setDoubleBufferingEnabled(boolean aFlag) {
        doubleBufferingEnabled = aFlag;
    }
    
    public boolean isDoubleBufferingEnabled() {
        return doubleBufferingEnabled;
    }
    
    void resetDoubleBuffer() {
        if (standardDoubleBuffer != null) {
            standardDoubleBuffer.needsReset = true;
        }
    }
    
    void resetVolatileDoubleBuffer(GraphicsConfiguration gc) {
        Image image = (Image)(Image)volatileMap.remove(gc);
        if (image != null) {
            image.flush();
        }
    }
    
    boolean useVolatileDoubleBuffer() {
        return volatileImageBufferEnabled;
    }
    {
    }
}
