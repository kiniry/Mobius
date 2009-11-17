package javax.swing.plaf.metal;

import javax.swing.plaf.*;
import javax.swing.*;
import java.awt.*;

class DefaultMetalTheme$FontDelegate {
    private static int[] defaultMapping = {0, 1, 2, 0, 0, 5};
    FontUIResource[] fonts;
    
    public DefaultMetalTheme$FontDelegate() {
        
        fonts = new FontUIResource[6];
    }
    
    public FontUIResource getFont(int type) {
        int mappedType = defaultMapping[type];
        if (fonts[type] == null) {
            Font f = getPrivilegedFont(mappedType);
            if (f == null) {
                f = new Font(DefaultMetalTheme.getDefaultFontName(type), DefaultMetalTheme.getDefaultFontStyle(type), DefaultMetalTheme.getDefaultFontSize(type));
            }
            fonts[type] = new FontUIResource(f);
        }
        return fonts[type];
    }
    
    protected Font getPrivilegedFont(final int key) {
        return (Font)(Font)java.security.AccessController.doPrivileged(new DefaultMetalTheme$FontDelegate$1(this, key));
    }
}
