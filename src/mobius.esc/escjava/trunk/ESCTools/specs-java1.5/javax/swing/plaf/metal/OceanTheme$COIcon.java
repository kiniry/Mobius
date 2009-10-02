package javax.swing.plaf.metal;

import java.awt.*;
import java.util.*;
import javax.swing.*;
import javax.swing.plaf.*;

class OceanTheme$COIcon extends IconUIResource {
    private Icon rtl;
    
    public OceanTheme$COIcon(Icon ltr, Icon rtl) {
        super(ltr);
        this.rtl = rtl;
    }
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        if (MetalUtils.isLeftToRight(c)) {
            super.paintIcon(c, g, x, y);
        } else {
            rtl.paintIcon(c, g, x, y);
        }
    }
}
