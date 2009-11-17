package javax.swing.plaf.metal;

import javax.swing.*;
import javax.swing.plaf.UIResource;
import java.awt.*;
import java.io.Serializable;

class MetalIconFactory$InternalFrameCloseIcon implements Icon, UIResource, Serializable {
    int iconSize = 16;
    
    public MetalIconFactory$InternalFrameCloseIcon(int size) {
        
        iconSize = size;
    }
    
    public void paintIcon(Component c, Graphics g, int x, int y) {
        JButton parentButton = (JButton)(JButton)c;
        ButtonModel buttonModel = parentButton.getModel();
        Color backgroundColor = MetalLookAndFeel.getPrimaryControl();
        Color internalBackgroundColor = MetalLookAndFeel.getPrimaryControl();
        Color mainItemColor = MetalLookAndFeel.getPrimaryControlDarkShadow();
        Color darkHighlightColor = MetalLookAndFeel.getBlack();
        Color xLightHighlightColor = MetalLookAndFeel.getWhite();
        Color boxLightHighlightColor = MetalLookAndFeel.getWhite();
        if (parentButton.getClientProperty("paintActive") != Boolean.TRUE) {
            backgroundColor = MetalLookAndFeel.getControl();
            internalBackgroundColor = backgroundColor;
            mainItemColor = MetalLookAndFeel.getControlDarkShadow();
            if (buttonModel.isPressed() && buttonModel.isArmed()) {
                internalBackgroundColor = MetalLookAndFeel.getControlShadow();
                xLightHighlightColor = internalBackgroundColor;
                mainItemColor = darkHighlightColor;
            }
        } else if (buttonModel.isPressed() && buttonModel.isArmed()) {
            internalBackgroundColor = MetalLookAndFeel.getPrimaryControlShadow();
            xLightHighlightColor = internalBackgroundColor;
            mainItemColor = darkHighlightColor;
        }
        int oneHalf = (int)(iconSize / 2);
        g.translate(x, y);
        g.setColor(backgroundColor);
        g.fillRect(0, 0, iconSize, iconSize);
        g.setColor(internalBackgroundColor);
        g.fillRect(3, 3, iconSize - 6, iconSize - 6);
        g.setColor(darkHighlightColor);
        g.drawRect(1, 1, iconSize - 3, iconSize - 3);
        g.drawRect(2, 2, iconSize - 5, iconSize - 5);
        g.setColor(boxLightHighlightColor);
        g.drawRect(2, 2, iconSize - 3, iconSize - 3);
        g.setColor(mainItemColor);
        g.drawRect(2, 2, iconSize - 4, iconSize - 4);
        g.drawLine(3, iconSize - 3, 3, iconSize - 3);
        g.drawLine(iconSize - 3, 3, iconSize - 3, 3);
        g.setColor(darkHighlightColor);
        g.drawLine(4, 5, 5, 4);
        g.drawLine(4, iconSize - 6, iconSize - 6, 4);
        g.setColor(xLightHighlightColor);
        g.drawLine(6, iconSize - 5, iconSize - 5, 6);
        g.drawLine(oneHalf, oneHalf + 2, oneHalf + 2, oneHalf);
        g.drawLine(iconSize - 5, iconSize - 5, iconSize - 4, iconSize - 5);
        g.drawLine(iconSize - 5, iconSize - 4, iconSize - 5, iconSize - 4);
        g.setColor(mainItemColor);
        g.drawLine(5, 5, iconSize - 6, iconSize - 6);
        g.drawLine(6, 5, iconSize - 5, iconSize - 6);
        g.drawLine(5, 6, iconSize - 6, iconSize - 5);
        g.drawLine(5, iconSize - 5, iconSize - 5, 5);
        g.drawLine(5, iconSize - 6, iconSize - 6, 5);
        g.translate(-x, -y);
    }
    
    public int getIconWidth() {
        return iconSize;
    }
    
    public int getIconHeight() {
        return iconSize;
    }
}
