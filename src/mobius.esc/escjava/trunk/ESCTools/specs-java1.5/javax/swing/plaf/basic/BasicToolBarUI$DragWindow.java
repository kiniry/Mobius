package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.border.*;
import javax.swing.plaf.*;

public class BasicToolBarUI$DragWindow extends Window {
    /*synthetic*/ final BasicToolBarUI this$0;
    Color borderColor = Color.gray;
    int orientation = this$0.toolBar.getOrientation();
    Point offset;
    
    BasicToolBarUI$DragWindow(/*synthetic*/ final BasicToolBarUI this$0, Window w) {
        super(w);
        this.this$0 = this$0;
    }
    
    public void setOrientation(int o) {
        if (isShowing()) {
            if (o == this.orientation) return;
            this.orientation = o;
            Dimension size = getSize();
            setSize(new Dimension(size.height, size.width));
            if (offset != null) {
                if (BasicGraphicsUtils.isLeftToRight(this$0.toolBar)) {
                    setOffset(new Point(offset.y, offset.x));
                } else if (o == JToolBar.HORIZONTAL) {
                    setOffset(new Point(size.height - offset.y, offset.x));
                } else {
                    setOffset(new Point(offset.y, size.width - offset.x));
                }
            }
            repaint();
        }
    }
    
    public Point getOffset() {
        return offset;
    }
    
    public void setOffset(Point p) {
        this.offset = p;
    }
    
    public void setBorderColor(Color c) {
        if (this.borderColor == c) return;
        this.borderColor = c;
        repaint();
    }
    
    public Color getBorderColor() {
        return this.borderColor;
    }
    
    public void paint(Graphics g) {
        this$0.paintDragWindow(g);
        super.paint(g);
    }
    
    public Insets getInsets() {
        return new Insets(1, 1, 1, 1);
    }
}
