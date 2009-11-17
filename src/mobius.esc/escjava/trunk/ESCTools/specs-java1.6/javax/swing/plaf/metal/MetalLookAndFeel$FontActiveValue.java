package javax.swing.plaf.metal;

import java.awt.*;
import javax.swing.plaf.*;
import javax.swing.*;
import javax.swing.plaf.basic.*;
import javax.swing.border.*;
import java.util.*;
import java.lang.reflect.*;

class MetalLookAndFeel$FontActiveValue implements UIDefaults$ActiveValue {
    private int type;
    private MetalTheme theme;
    
    MetalLookAndFeel$FontActiveValue(MetalTheme theme, int type) {
        
        this.theme = theme;
        this.type = type;
    }
    
    public Object createValue(UIDefaults table) {
        Object value = null;
        switch (type) {
        case MetalTheme.CONTROL_TEXT_FONT: 
            value = theme.getControlTextFont();
            break;
        
        case MetalTheme.SYSTEM_TEXT_FONT: 
            value = theme.getSystemTextFont();
            break;
        
        case MetalTheme.USER_TEXT_FONT: 
            value = theme.getUserTextFont();
            break;
        
        case MetalTheme.MENU_TEXT_FONT: 
            value = theme.getMenuTextFont();
            break;
        
        case MetalTheme.WINDOW_TITLE_FONT: 
            value = theme.getWindowTitleFont();
            break;
        
        case MetalTheme.SUB_TEXT_FONT: 
            value = theme.getSubTextFont();
            break;
        
        }
        return value;
    }
}
