package javax.swing;

import java.awt.*;

public class PopupFactory {
    {
    }
    
    public PopupFactory() {
        
    }
    private static final Object SharedInstanceKey = new StringBuffer("PopupFactory.SharedInstanceKey");
    private static final int MAX_CACHE_SIZE = 5;
    static final int LIGHT_WEIGHT_POPUP = 0;
    static final int MEDIUM_WEIGHT_POPUP = 1;
    static final int HEAVY_WEIGHT_POPUP = 2;
    private int popupType = LIGHT_WEIGHT_POPUP;
    static final StringBuffer forceHeavyWeightPopupKey = new StringBuffer("__force_heavy_weight_popup__");
    
    public static void setSharedInstance(PopupFactory factory) {
        if (factory == null) {
            throw new IllegalArgumentException("PopupFactory can not be null");
        }
        SwingUtilities.appContextPut(SharedInstanceKey, factory);
    }
    
    public static PopupFactory getSharedInstance() {
        PopupFactory factory = (PopupFactory)(PopupFactory)SwingUtilities.appContextGet(SharedInstanceKey);
        if (factory == null) {
            factory = new PopupFactory();
            setSharedInstance(factory);
        }
        return factory;
    }
    
    void setPopupType(int type) {
        popupType = type;
    }
    
    int getPopupType() {
        return popupType;
    }
    
    public Popup getPopup(Component owner, Component contents, int x, int y) throws IllegalArgumentException {
        if (contents == null) {
            throw new IllegalArgumentException("Popup.getPopup must be passed non-null contents");
        }
        int popupType = getPopupType(owner, contents, x, y);
        Popup popup = getPopup(owner, contents, x, y, popupType);
        if (popup == null) {
            popup = getPopup(owner, contents, x, y, HEAVY_WEIGHT_POPUP);
        }
        return popup;
    }
    
    private int getPopupType(Component owner, Component contents, int ownerX, int ownerY) {
        int popupType = getPopupType();
        if (owner == null || invokerInHeavyWeightPopup(owner)) {
            popupType = HEAVY_WEIGHT_POPUP;
        } else if (popupType == LIGHT_WEIGHT_POPUP && !(contents instanceof JToolTip) && !(contents instanceof JPopupMenu)) {
            popupType = MEDIUM_WEIGHT_POPUP;
        }
        Component c = owner;
        while (c != null) {
            if (c instanceof JComponent) {
                if (((JComponent)(JComponent)c).getClientProperty(forceHeavyWeightPopupKey) == Boolean.TRUE) {
                    popupType = HEAVY_WEIGHT_POPUP;
                    break;
                }
            }
            c = c.getParent();
        }
        return popupType;
    }
    
    private Popup getPopup(Component owner, Component contents, int ownerX, int ownerY, int popupType) {
        if (GraphicsEnvironment.isHeadless()) {
            return getHeadlessPopup(owner, contents, ownerX, ownerY);
        }
        switch (popupType) {
        case LIGHT_WEIGHT_POPUP: 
            return getLightWeightPopup(owner, contents, ownerX, ownerY);
        
        case MEDIUM_WEIGHT_POPUP: 
            return getMediumWeightPopup(owner, contents, ownerX, ownerY);
        
        case HEAVY_WEIGHT_POPUP: 
            return getHeavyWeightPopup(owner, contents, ownerX, ownerY);
        
        }
        return null;
    }
    
    private Popup getHeadlessPopup(Component owner, Component contents, int ownerX, int ownerY) {
        return PopupFactory$HeadlessPopup.getHeadlessPopup(owner, contents, ownerX, ownerY);
    }
    
    private Popup getLightWeightPopup(Component owner, Component contents, int ownerX, int ownerY) {
        return PopupFactory$LightWeightPopup.getLightWeightPopup(owner, contents, ownerX, ownerY);
    }
    
    private Popup getMediumWeightPopup(Component owner, Component contents, int ownerX, int ownerY) {
        return PopupFactory$MediumWeightPopup.getMediumWeightPopup(owner, contents, ownerX, ownerY);
    }
    
    private Popup getHeavyWeightPopup(Component owner, Component contents, int ownerX, int ownerY) {
        if (GraphicsEnvironment.isHeadless()) {
            return getMediumWeightPopup(owner, contents, ownerX, ownerY);
        }
        return PopupFactory$HeavyWeightPopup.getHeavyWeightPopup(owner, contents, ownerX, ownerY);
    }
    
    private boolean invokerInHeavyWeightPopup(Component i) {
        if (i != null) {
            Container parent;
            for (parent = i.getParent(); parent != null; parent = parent.getParent()) {
                if (parent instanceof Popup$HeavyWeightWindow) {
                    return true;
                }
            }
        }
        return false;
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
}
