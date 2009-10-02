package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import javax.swing.text.*;
import javax.swing.*;
import javax.swing.border.*;
import javax.swing.event.*;
import java.util.*;

class HiddenTagView$StartTagBorder implements Border, Serializable {
    
    HiddenTagView$StartTagBorder() {
        
    }
    
    public void paintBorder(Component c, Graphics g, int x, int y, int width, int height) {
        g.setColor(HiddenTagView.UnknownTagBorderColor);
        x += 3;
        width -= (3 * 2);
        g.drawLine(x, y + 3, x, y + height - 3);
        g.drawArc(x, y + height - 6 - 1, 6, 6, 180, 90);
        g.drawArc(x, y, 6, 6, 90, 90);
        g.drawLine(x + 3, y, x + width - 6, y);
        g.drawLine(x + 3, y + height - 1, x + width - 6, y + height - 1);
        g.drawLine(x + width - 6, y, x + width - 1, y + height / 2);
        g.drawLine(x + width - 6, y + height, x + width - 1, y + height / 2);
    }
    
    public Insets getBorderInsets(Component c) {
        return new Insets(2, 2 + 3, 2, 6 + 2 + 3);
    }
    
    public boolean isBorderOpaque() {
        return false;
    }
}
