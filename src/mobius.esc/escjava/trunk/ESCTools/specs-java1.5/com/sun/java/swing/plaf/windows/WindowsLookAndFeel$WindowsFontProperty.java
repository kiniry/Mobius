package com.sun.java.swing.plaf.windows;

import java.awt.*;
import javax.swing.plaf.*;
import javax.swing.*;
import javax.swing.plaf.basic.*;
import javax.swing.border.*;
import java.awt.Font;
import java.util.*;
import sun.font.FontManager;
import com.sun.java.swing.plaf.windows.TMSchema.*;

class WindowsLookAndFeel$WindowsFontProperty extends DesktopProperty {
    
    WindowsLookAndFeel$WindowsFontProperty(String key, Object backup, Toolkit kit) {
        super(key, backup, kit);
    }
    
    protected Object configureValue(Object value) {
        if (value instanceof Font) {
            Font font = (Font)(Font)value;
            if ("MS Sans Serif".equals(font.getName())) {
                int size = font.getSize();
                int dpi;
                try {
                    dpi = Toolkit.getDefaultToolkit().getScreenResolution();
                } catch (HeadlessException ex) {
                    dpi = 96;
                }
                if (Math.round(size * 72.0F / dpi) < 8) {
                    size = Math.round(8 * dpi / 72.0F);
                }
                Font msFont = new FontUIResource("Microsoft Sans Serif", font.getStyle(), size);
                if (msFont.getName() != null && msFont.getName().equals(msFont.getFamily())) {
                    font = msFont;
                } else if (size != font.getSize()) {
                    font = new FontUIResource("MS Sans Serif", font.getStyle(), size);
                }
            }
            if (FontManager.fontSupportsDefaultEncoding(font)) {
                if (!(font instanceof UIResource)) {
                    font = new FontUIResource(font);
                }
            } else {
                font = FontManager.getCompositeFontUIResource(font);
            }
            return font;
        }
        return super.configureValue(value);
    }
}
