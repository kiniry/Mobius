package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import javax.swing.text.*;
import javax.swing.*;
import javax.swing.border.*;
import javax.swing.event.*;
import java.util.*;

class CommentView$CommentBorder extends LineBorder {
    
    CommentView$CommentBorder() {
        super(Color.black, 1);
    }
    
    public void paintBorder(Component c, Graphics g, int x, int y, int width, int height) {
        super.paintBorder(c, g, x + 3, y, width - 9, height);
    }
    
    public Insets getBorderInsets(Component c) {
        Insets retI = super.getBorderInsets(c);
        retI.left += 3;
        retI.right += 3;
        return retI;
    }
    
    public boolean isBorderOpaque() {
        return false;
    }
}
