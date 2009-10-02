package javax.swing;

import java.awt.*;
import java.util.ArrayList;
import java.util.List;

class PopupFactory$LightWeightPopup extends PopupFactory$ContainerPopup {
    
    private PopupFactory$LightWeightPopup() {
        super(null);
    }
    private static final Object lightWeightPopupCacheKey = new StringBuffer("PopupFactory.lightPopupCache");
    
    static Popup getLightWeightPopup(Component owner, Component contents, int ownerX, int ownerY) {
        PopupFactory$LightWeightPopup popup = getRecycledLightWeightPopup();
        if (popup == null) {
            popup = new PopupFactory$LightWeightPopup();
        }
        popup.reset(owner, contents, ownerX, ownerY);
        if (!popup.fitsOnScreen() || popup.overlappedByOwnedWindow()) {
            popup.hide();
            return null;
        }
        return popup;
    }
    
    private static List getLightWeightPopupCache() {
        List cache = (List)(List)SwingUtilities.appContextGet(lightWeightPopupCacheKey);
        if (cache == null) {
            cache = new ArrayList();
            SwingUtilities.appContextPut(lightWeightPopupCacheKey, cache);
        }
        return cache;
    }
    
    private static void recycleLightWeightPopup(PopupFactory$LightWeightPopup popup) {
        synchronized (PopupFactory.LightWeightPopup.class) {
            List lightPopupCache = getLightWeightPopupCache();
            if (lightPopupCache.size() < 5) {
                lightPopupCache.add(popup);
            }
        }
    }
    
    private static PopupFactory$LightWeightPopup getRecycledLightWeightPopup() {
        synchronized (PopupFactory.LightWeightPopup.class) {
            List lightPopupCache = getLightWeightPopupCache();
            int c;
            if ((c = lightPopupCache.size()) > 0) {
                PopupFactory$LightWeightPopup r = (PopupFactory$LightWeightPopup)(PopupFactory$LightWeightPopup)lightPopupCache.get(0);
                lightPopupCache.remove(0);
                return r;
            }
            return null;
        }
    }
    
    public void hide() {
        super.hide();
        Container component = (Container)(Container)getComponent();
        component.removeAll();
        recycleLightWeightPopup(this);
    }
    
    public void show() {
        Container parent = null;
        if (owner != null) {
            parent = (owner instanceof Container ? (Container)(Container)owner : owner.getParent());
        }
        for (Container p = parent; p != null; p = p.getParent()) {
            if (p instanceof JRootPane) {
                if (p.getParent() instanceof JInternalFrame) {
                    continue;
                }
                parent = ((JRootPane)(JRootPane)p).getLayeredPane();
            } else if (p instanceof Window) {
                if (parent == null) {
                    parent = p;
                }
                break;
            } else if (p instanceof JApplet) {
                break;
            }
        }
        Point p = SwingUtilities.convertScreenLocationToParent(parent, x, y);
        Component component = getComponent();
        component.setLocation(p.x, p.y);
        if (parent instanceof JLayeredPane) {
            ((JLayeredPane)(JLayeredPane)parent).add(component, JLayeredPane.POPUP_LAYER, 0);
        } else {
            parent.add(component);
        }
    }
    
    Component createComponent(Component owner) {
        JComponent component = new JPanel(new BorderLayout(), true);
        component.setOpaque(true);
        return component;
    }
    
    void reset(Component owner, Component contents, int ownerX, int ownerY) {
        super.reset(owner, contents, ownerX, ownerY);
        JComponent component = (JComponent)(JComponent)getComponent();
        component.setLocation(ownerX, ownerY);
        component.add(contents, BorderLayout.CENTER);
        contents.invalidate();
        pack();
    }
}
