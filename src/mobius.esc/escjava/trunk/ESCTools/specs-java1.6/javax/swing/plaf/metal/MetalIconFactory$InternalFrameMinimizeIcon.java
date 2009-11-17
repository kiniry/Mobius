package javax.swing.plaf.metal;

import javax.swing.*;
import javax.swing.plaf.UIResource;
import java.awt.*;
import java.io.Serializable;

class MetalIconFactory$InternalFrameMinimizeIcon implements Icon, UIResource, Serializable {
    int iconSize = 16;
    
    public MetalIconFactory$InternalFrameMinimizeIcon(int size) {
        
        iconSize = size;
    }
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        JButton parentButton = (JButton)(JButton)c;
        ButtonModel buttonModel = parentButton.getModel();
        Color backgroundColor = MetalLookAndFeel.getPrimaryControl();
        Color internalBackgroundColor = MetalLookAndFeel.getPrimaryControl();
        Color mainItemColor = MetalLookAndFeel.getPrimaryControlDarkShadow();
        Color darkHighlightColor = MetalLookAndFeel.getBlack();
        Color ulLightHighlightColor = MetalLookAndFeel.getWhite();
        Color lrLightHighlightColor = MetalLookAndFeel.getWhite();
        if (parentButton.getClientProperty("paintActive") != Boolean.TRUE) {
            backgroundColor = MetalLookAndFeel.getControl();
            internalBackgroundColor = backgroundColor;
            mainItemColor = MetalLookAndFeel.getControlDarkShadow();
            if (buttonModel.isPressed() && buttonModel.isArmed()) {
                internalBackgroundColor = MetalLookAndFeel.getControlShadow();
                ulLightHighlightColor = internalBackgroundColor;
                mainItemColor = darkHighlightColor;
            }
        } else if (buttonModel.isPressed() && buttonModel.isArmed()) {
            internalBackgroundColor = MetalLookAndFeel.getPrimaryControlShadow();
            ulLightHighlightColor = internalBackgroundColor;
            mainItemColor = darkHighlightColor;
        }
        g.translate(x, y);
        g.setColor(backgroundColor);
        g.fillRect(0, 0, iconSize, iconSize);
        g.setColor(internalBackgroundColor);
        g.fillRect(4, 11, iconSize - 13, iconSize - 13);
        g.setColor(lrLightHighlightColor);
        g.drawRect(2, 10, iconSize - 10, iconSize - 11);
        g.setColor(ulLightHighlightColor);
        g.drawRect(3, 10, iconSize - 12, iconSize - 12);
        g.setColor(darkHighlightColor);
        g.drawRect(1, 8, iconSize - 10, iconSize - 10);
        g.drawRect(2, 9, iconSize - 12, iconSize - 12);
        g.setColor(mainItemColor);
        g.drawRect(2, 9, iconSize - 11, iconSize - 11);
        g.drawLine(iconSize - 10, 10, iconSize - 10, 10);
        g.drawLine(3, iconSize - 3, 3, iconSize - 3);
        g.setColor(mainItemColor);
        g.fillRect(iconSize - 7, 3, 3, 5);
        g.drawLine(iconSize - 6, 5, iconSize - 3, 2);
        g.drawLine(iconSize - 6, 6, iconSize - 2, 2);
        g.drawLine(iconSize - 6, 7, iconSize - 3, 7);
        g.setColor(darkHighlightColor);
        g.drawLine(iconSize - 8, 2, iconSize - 7, 2);
        g.drawLine(iconSize - 8, 3, iconSize - 8, 7);
        g.drawLine(iconSize - 6, 4, iconSize - 3, 1);
        g.drawLine(iconSize - 4, 6, iconSize - 3, 6);
        g.setColor(lrLightHighlightColor);
        g.drawLine(iconSize - 6, 3, iconSize - 6, 3);
        g.drawLine(iconSize - 4, 5, iconSize - 2, 3);
        g.drawLine(iconSize - 7, 8, iconSize - 3, 8);
        g.drawLine(iconSize - 2, 8, iconSize - 2, 7);
        g.translate(-x, -y);
    }
    
    public int getIconWidth() {
        return iconSize;
    }
    
    public int getIconHeight() {
        return iconSize;
    }
}
