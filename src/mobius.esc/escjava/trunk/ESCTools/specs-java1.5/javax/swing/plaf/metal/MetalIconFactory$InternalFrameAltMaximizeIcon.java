package javax.swing.plaf.metal;

import javax.swing.*;
import javax.swing.plaf.UIResource;
import java.awt.*;
import java.io.Serializable;

class MetalIconFactory$InternalFrameAltMaximizeIcon implements Icon, UIResource, Serializable {
    int iconSize = 16;
    
    public MetalIconFactory$InternalFrameAltMaximizeIcon(int size) {
        
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
        g.fillRect(3, 6, iconSize - 9, iconSize - 9);
        g.setColor(darkHighlightColor);
        g.drawRect(1, 5, iconSize - 8, iconSize - 8);
        g.drawLine(1, iconSize - 2, 1, iconSize - 2);
        g.setColor(lrLightHighlightColor);
        g.drawRect(2, 6, iconSize - 7, iconSize - 7);
        g.setColor(ulLightHighlightColor);
        g.drawRect(3, 7, iconSize - 9, iconSize - 9);
        g.setColor(mainItemColor);
        g.drawRect(2, 6, iconSize - 8, iconSize - 8);
        g.setColor(ulLightHighlightColor);
        g.drawLine(iconSize - 6, 8, iconSize - 6, 8);
        g.drawLine(iconSize - 9, 6, iconSize - 7, 8);
        g.setColor(mainItemColor);
        g.drawLine(3, iconSize - 3, 3, iconSize - 3);
        g.setColor(darkHighlightColor);
        g.drawLine(iconSize - 6, 9, iconSize - 6, 9);
        g.setColor(backgroundColor);
        g.drawLine(iconSize - 9, 5, iconSize - 9, 5);
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
        g.drawLine(iconSize - 4, 8, iconSize - 3, 8);
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
