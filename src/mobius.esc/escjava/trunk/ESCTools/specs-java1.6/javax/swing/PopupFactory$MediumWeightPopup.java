package javax.swing;

import java.applet.Applet;
import java.awt.*;
import java.util.ArrayList;
import java.util.List;

class PopupFactory$MediumWeightPopup extends PopupFactory$ContainerPopup {
    
    private PopupFactory$MediumWeightPopup() {
        super(null);
    }
    private static final Object mediumWeightPopupCacheKey = new StringBuffer("PopupFactory.mediumPopupCache");
    private JRootPane rootPane;
    
    static Popup getMediumWeightPopup(Component owner, Component contents, int ownerX, int ownerY) {
        PopupFactory$MediumWeightPopup popup = getRecycledMediumWeightPopup();
        if (popup == null) {
            popup = new PopupFactory$MediumWeightPopup();
        }
        popup.reset(owner, contents, ownerX, ownerY);
        if (!popup.fitsOnScreen() || popup.overlappedByOwnedWindow()) {
            popup.hide();
            return null;
        }
        return popup;
    }
    
    private static List getMediumWeightPopupCache() {
        List cache = (List)(List)SwingUtilities.appContextGet(mediumWeightPopupCacheKey);
        if (cache == null) {
            cache = new ArrayList();
            SwingUtilities.appContextPut(mediumWeightPopupCacheKey, cache);
        }
        return cache;
    }
    
    private static void recycleMediumWeightPopup(PopupFactory$MediumWeightPopup popup) {
        synchronized (PopupFactory.MediumWeightPopup.class) {
            List mediumPopupCache = getMediumWeightPopupCache();
            if (mediumPopupCache.size() < 5) {
                mediumPopupCache.add(popup);
            }
        }
    }
    
    private static PopupFactory$MediumWeightPopup getRecycledMediumWeightPopup() {
        synchronized (PopupFactory.MediumWeightPopup.class) {
            java.util.List mediumPopupCache = getMediumWeightPopupCache();
            int c;
            if ((c = mediumPopupCache.size()) > 0) {
                PopupFactory$MediumWeightPopup r = (PopupFactory$MediumWeightPopup)(PopupFactory$MediumWeightPopup)mediumPopupCache.get(0);
                mediumPopupCache.remove(0);
                return r;
            }
            return null;
        }
    }
    
    public void hide() {
        super.hide();
        rootPane.getContentPane().removeAll();
        recycleMediumWeightPopup(this);
    }
    
    public void show() {
        Component component = getComponent();
        Container parent = null;
        if (owner != null) {
            parent = owner.getParent();
        }
        while (!(parent instanceof Window || parent instanceof Applet) && (parent != null)) {
            parent = parent.getParent();
        }
        if (parent instanceof RootPaneContainer) {
            parent = ((RootPaneContainer)(RootPaneContainer)parent).getLayeredPane();
            Point p = SwingUtilities.convertScreenLocationToParent(parent, x, y);
            component.setVisible(false);
            component.setLocation(p.x, p.y);
            ((JLayeredPane)(JLayeredPane)parent).add(component, JLayeredPane.POPUP_LAYER, 0);
        } else {
            Point p = SwingUtilities.convertScreenLocationToParent(parent, x, y);
            component.setLocation(p.x, p.y);
            component.setVisible(false);
            parent.add(component);
        }
        component.setVisible(true);
    }
    
    Component createComponent(Component owner) {
        Panel component = new Panel(new BorderLayout());
        rootPane = new JRootPane();
        rootPane.setOpaque(true);
        component.add(rootPane, BorderLayout.CENTER);
        return component;
    }
    
    void reset(Component owner, Component contents, int ownerX, int ownerY) {
        super.reset(owner, contents, ownerX, ownerY);
        Component component = getComponent();
        component.setLocation(ownerX, ownerY);
        rootPane.getContentPane().add(contents, BorderLayout.CENTER);
        contents.invalidate();
        component.validate();
        pack();
    }
}
