package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import javax.swing.text.*;
import javax.swing.*;
import javax.swing.border.*;
import javax.swing.event.*;
import java.util.*;

class HiddenTagView$EndTagBorder implements Border, Serializable {
    
    HiddenTagView$EndTagBorder() {
        
    }
    
    public void paintBorder(Component c, Graphics g, int x, int y, int width, int height) {
        g.setColor(HiddenTagView.UnknownTagBorderColor);
        x += 3;
        width -= (3 * 2);
        g.drawLine(x + width - 1, y + 3, x + width - 1, y + height - 3);
        g.drawArc(x + width - 6 - 1, y + height - 6 - 1, 6, 6, 270, 90);
        g.drawArc(x + width - 6 - 1, y, 6, 6, 0, 90);
        g.drawLine(x + 6, y, x + width - 3, y);
        g.drawLine(x + 6, y + height - 1, x + width - 3, y + height - 1);
        g.drawLine(x + 6, y, x, y + height / 2);
        g.drawLine(x + 6, y + height, x, y + height / 2);
    }
    
    public Insets getBorderInsets(Component c) {
        return new Insets(2, 6 + 2 + 3, 2, 2 + 3);
    }
    
    public boolean isBorderOpaque() {
        return false;
    }
}
