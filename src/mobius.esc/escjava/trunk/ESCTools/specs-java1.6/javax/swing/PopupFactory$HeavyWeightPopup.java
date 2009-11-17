package javax.swing;

import java.awt.*;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

class PopupFactory$HeavyWeightPopup extends Popup {
    
    /*synthetic*/ static Map access$000() {
        return getHeavyWeightPopupCache();
    }
    
    private PopupFactory$HeavyWeightPopup() {
        
    }
    private static final Object heavyWeightPopupCacheKey = new StringBuffer("PopupFactory.heavyWeightPopupCache");
    
    static Popup getHeavyWeightPopup(Component owner, Component contents, int ownerX, int ownerY) {
        Window window = (owner != null) ? SwingUtilities.getWindowAncestor(owner) : null;
        PopupFactory$HeavyWeightPopup popup = null;
        if (window != null) {
            popup = getRecycledHeavyWeightPopup(window);
        }
        boolean focusPopup = false;
        if (contents != null && contents.isFocusable()) {
            if (contents instanceof JPopupMenu) {
                JPopupMenu jpm = (JPopupMenu)(JPopupMenu)contents;
                Component[] popComps = jpm.getComponents();
                for (int i = 0; i < popComps.length; i++) {
                    if (!(popComps[i] instanceof MenuElement) && !(popComps[i] instanceof JSeparator)) {
                        focusPopup = true;
                        break;
                    }
                }
            }
        }
        if (popup == null || ((JWindow)(JWindow)popup.getComponent()).getFocusableWindowState() != focusPopup) {
            if (popup != null) {
                popup._dispose();
            }
            popup = new PopupFactory$HeavyWeightPopup();
        }
        popup.reset(owner, contents, ownerX, ownerY);
        if (focusPopup) {
            JWindow wnd = (JWindow)(JWindow)popup.getComponent();
            wnd.setFocusableWindowState(true);
            wnd.setName("###focusableSwingPopup###");
        }
        return popup;
    }
    
    private static PopupFactory$HeavyWeightPopup getRecycledHeavyWeightPopup(Window w) {
        synchronized (PopupFactory.HeavyWeightPopup.class) {
            List cache;
            Map heavyPopupCache = getHeavyWeightPopupCache();
            if (heavyPopupCache.containsKey(w)) {
                cache = (List)(List)heavyPopupCache.get(w);
            } else {
                return null;
            }
            int c;
            if ((c = cache.size()) > 0) {
                PopupFactory$HeavyWeightPopup r = (PopupFactory$HeavyWeightPopup)(PopupFactory$HeavyWeightPopup)cache.get(0);
                cache.remove(0);
                return r;
            }
            return null;
        }
    }
    
    private static Map getHeavyWeightPopupCache() {
        synchronized (PopupFactory.HeavyWeightPopup.class) {
            Map cache = (Map)(Map)SwingUtilities.appContextGet(heavyWeightPopupCacheKey);
            if (cache == null) {
                cache = new HashMap(2);
                SwingUtilities.appContextPut(heavyWeightPopupCacheKey, cache);
            }
            return cache;
        }
    }
    
    private static void recycleHeavyWeightPopup(PopupFactory$HeavyWeightPopup popup) {
        synchronized (PopupFactory.HeavyWeightPopup.class) {
            List cache;
            Object window = SwingUtilities.getWindowAncestor(popup.getComponent());
            Map heavyPopupCache = getHeavyWeightPopupCache();
            if (window instanceof Popup$DefaultFrame || !((Window)(Window)window).isVisible()) {
                popup._dispose();
                return;
            } else if (heavyPopupCache.containsKey(window)) {
                cache = (List)(List)heavyPopupCache.get(window);
            } else {
                cache = new ArrayList();
                heavyPopupCache.put(window, cache);
                final Window w = (Window)(Window)window;
                w.addWindowListener(new PopupFactory$HeavyWeightPopup$1(w));
            }
            if (cache.size() < 5) {
                cache.add(popup);
            } else {
                popup._dispose();
            }
        }
    }
    
    public void hide() {
        super.hide();
        recycleHeavyWeightPopup(this);
    }
    
    void dispose() {
    }
    
    void _dispose() {
        super.dispose();
    }
}
