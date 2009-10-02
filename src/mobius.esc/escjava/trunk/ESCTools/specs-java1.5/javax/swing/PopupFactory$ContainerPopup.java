package javax.swing;

import java.applet.Applet;
import java.awt.*;

class PopupFactory$ContainerPopup extends Popup {
    
    /*synthetic*/ PopupFactory$ContainerPopup(javax.swing.PopupFactory$1 x0) {
        this();
    }
    
    private PopupFactory$ContainerPopup() {
        
    }
    Component owner;
    int x;
    int y;
    
    public void hide() {
        Component component = getComponent();
        if (component != null) {
            Container parent = component.getParent();
            if (parent != null) {
                Rectangle bounds = component.getBounds();
                parent.remove(component);
                parent.repaint(bounds.x, bounds.y, bounds.width, bounds.height);
            }
        }
        owner = null;
    }
    
    public void pack() {
        Component component = getComponent();
        if (component != null) {
            component.setSize(component.getPreferredSize());
        }
    }
    
    void reset(Component owner, Component contents, int ownerX, int ownerY) {
        if ((owner instanceof JFrame) || (owner instanceof JDialog) || (owner instanceof JWindow)) {
            owner = ((RootPaneContainer)(RootPaneContainer)owner).getLayeredPane();
        }
        super.reset(owner, contents, ownerX, ownerY);
        x = ownerX;
        y = ownerY;
        this.owner = owner;
    }
    
    boolean overlappedByOwnedWindow() {
        Component component = getComponent();
        if (owner != null && component != null) {
            Window w = SwingUtilities.getWindowAncestor(owner);
            if (w == null) {
                return false;
            }
            Window[] ownedWindows = w.getOwnedWindows();
            if (ownedWindows != null) {
                Rectangle bnd = component.getBounds();
                for (int i = 0; i < ownedWindows.length; i++) {
                    Window owned = ownedWindows[i];
                    if (owned.isVisible() && bnd.intersects(owned.getBounds())) {
                        return true;
                    }
                }
            }
        }
        return false;
    }
    
    boolean fitsOnScreen() {
        Component component = getComponent();
        if (owner != null && component != null) {
            Container parent;
            int width = component.getWidth();
            int height = component.getHeight();
            for (parent = owner.getParent(); parent != null; parent = parent.getParent()) {
                if (parent instanceof JFrame || parent instanceof JDialog || parent instanceof JWindow) {
                    Rectangle r = parent.getBounds();
                    Insets i = parent.getInsets();
                    r.x += i.left;
                    r.y += i.top;
                    r.width -= (i.left + i.right);
                    r.height -= (i.top + i.bottom);
                    return SwingUtilities.isRectangleContainingRectangle(r, new Rectangle(x, y, width, height));
                } else if (parent instanceof JApplet) {
                    Rectangle r = parent.getBounds();
                    Point p = parent.getLocationOnScreen();
                    r.x = p.x;
                    r.y = p.y;
                    return SwingUtilities.isRectangleContainingRectangle(r, new Rectangle(x, y, width, height));
                } else if (parent instanceof Window || parent instanceof Applet) {
                    break;
                }
            }
        }
        return false;
    }
}
