package java.awt;

import java.util.Locale;
import java.util.ResourceBundle;

public final class ComponentOrientation implements java.io.Serializable {
    private static final int UNK_BIT = 1;
    private static final int HORIZ_BIT = 2;
    private static final int LTR_BIT = 4;
    public static final ComponentOrientation LEFT_TO_RIGHT = new ComponentOrientation(HORIZ_BIT | LTR_BIT);
    public static final ComponentOrientation RIGHT_TO_LEFT = new ComponentOrientation(HORIZ_BIT);
    public static final ComponentOrientation UNKNOWN = new ComponentOrientation(HORIZ_BIT | LTR_BIT | UNK_BIT);
    
    public boolean isHorizontal() {
        return (orientation & HORIZ_BIT) != 0;
    }
    
    public boolean isLeftToRight() {
        return (orientation & LTR_BIT) != 0;
    }
    
    public static ComponentOrientation getOrientation(Locale locale) {
        String lang = locale.getLanguage();
        if ("iw".equals(lang) || "ar".equals(lang) || "fa".equals(lang) || "ur".equals(lang)) {
            return RIGHT_TO_LEFT;
        } else {
            return LEFT_TO_RIGHT;
        }
    }
    
    
    public static ComponentOrientation getOrientation(ResourceBundle bdl) {
        ComponentOrientation result = null;
        try {
            result = (ComponentOrientation)(ComponentOrientation)bdl.getObject("Orientation");
        } catch (Exception e) {
        }
        if (result == null) {
            result = getOrientation(bdl.getLocale());
        }
        if (result == null) {
            result = getOrientation(Locale.getDefault());
        }
        return result;
    }
    private int orientation;
    
    private ComponentOrientation(int value) {
        
        orientation = value;
    }
}
