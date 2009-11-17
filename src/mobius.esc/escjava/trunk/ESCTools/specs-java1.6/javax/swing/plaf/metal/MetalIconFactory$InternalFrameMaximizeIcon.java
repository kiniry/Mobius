package javax.swing.plaf.metal;

import javax.swing.*;
import javax.swing.plaf.UIResource;
import java.awt.*;
import java.io.Serializable;

class MetalIconFactory$InternalFrameMaximizeIcon implements Icon, UIResource, Serializable {
    protected int iconSize = 16;
    
    public MetalIconFactory$InternalFrameMaximizeIcon(int size) {
        
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
        g.fillRect(3, 7, iconSize - 10, iconSize - 10);
        g.setColor(ulLightHighlightColor);
        g.drawRect(3, 7, iconSize - 10, iconSize - 10);
        g.setColor(lrLightHighlightColor);
        g.drawRect(2, 6, iconSize - 7, iconSize - 7);
        g.setColor(darkHighlightColor);
        g.drawRect(1, 5, iconSize - 7, iconSize - 7);
        g.drawRect(2, 6, iconSize - 9, iconSize - 9);
        g.setColor(mainItemColor);
        g.drawRect(2, 6, iconSize - 8, iconSize - 8);
        g.setColor(darkHighlightColor);
        g.drawLine(3, iconSize - 5, iconSize - 9, 7);
        g.drawLine(iconSize - 6, 4, iconSize - 5, 3);
        g.drawLine(iconSize - 7, 1, iconSize - 7, 2);
        g.drawLine(iconSize - 6, 1, iconSize - 2, 1);
        g.setColor(ulLightHighlightColor);
        g.drawLine(5, iconSize - 4, iconSize - 8, 9);
        g.setColor(lrLightHighlightColor);
        g.drawLine(iconSize - 6, 3, iconSize - 4, 5);
        g.drawLine(iconSize - 4, 5, iconSize - 4, 6);
        g.drawLine(iconSize - 2, 7, iconSize - 1, 7);
        g.drawLine(iconSize - 1, 2, iconSize - 1, 6);
        g.setColor(mainItemColor);
        g.drawLine(3, iconSize - 4, iconSize - 3, 2);
        g.drawLine(3, iconSize - 3, iconSize - 2, 2);
        g.drawLine(4, iconSize - 3, 5, iconSize - 3);
        g.drawLine(iconSize - 7, 8, iconSize - 7, 9);
        g.drawLine(iconSize - 6, 2, iconSize - 4, 2);
        g.drawRect(iconSize - 3, 3, 1, 3);
        g.translate(-x, -y);
    }
    
    public int getIconWidth() {
        return iconSize;
    }
    
    public int getIconHeight() {
        return iconSize;
    }
}
