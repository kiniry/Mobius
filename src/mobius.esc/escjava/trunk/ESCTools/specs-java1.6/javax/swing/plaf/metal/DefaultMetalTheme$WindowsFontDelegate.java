package javax.swing.plaf.metal;

import javax.swing.plaf.*;
import javax.swing.*;
import java.awt.*;

class DefaultMetalTheme$WindowsFontDelegate extends DefaultMetalTheme$FontDelegate {
    private MetalFontDesktopProperty[] props;
    private boolean[] checkedPriviledged;
    
    public DefaultMetalTheme$WindowsFontDelegate() {
        
        props = new MetalFontDesktopProperty[6];
        checkedPriviledged = new boolean[6];
    }
    
    public FontUIResource getFont(int type) {
        if (fonts[type] != null) {
            return fonts[type];
        }
        if (!checkedPriviledged[type]) {
            Font f = getPrivilegedFont(type);
            checkedPriviledged[type] = true;
            if (f != null) {
                fonts[type] = new FontUIResource(f);
                return fonts[type];
            }
        }
        if (props[type] == null) {
            props[type] = new MetalFontDesktopProperty(type);
        }
        return (FontUIResource)(FontUIResource)props[type].createValue(null);
    }
}
