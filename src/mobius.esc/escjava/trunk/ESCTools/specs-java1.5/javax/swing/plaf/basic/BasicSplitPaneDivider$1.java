package javax.swing.plaf.basic;

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.border.Border;
import java.beans.*;

class BasicSplitPaneDivider$1 extends JButton {
    /*synthetic*/ final BasicSplitPaneDivider this$0;
    
    BasicSplitPaneDivider$1(/*synthetic*/ final BasicSplitPaneDivider this$0) {
        this.this$0 = this$0;
        
    }
    
    public void setBorder(Border b) {
    }
    
    public void paint(Graphics g) {
        if (this$0.splitPane != null) {
            int[] xs = new int[3];
            int[] ys = new int[3];
            int blockSize;
            g.setColor(this.getBackground());
            g.fillRect(0, 0, this.getWidth(), this.getHeight());
            g.setColor(Color.black);
            if (this$0.orientation == JSplitPane.VERTICAL_SPLIT) {
                blockSize = Math.min(getHeight(), BasicSplitPaneDivider.access$000(this$0));
                xs[0] = blockSize;
                xs[1] = 0;
                xs[2] = blockSize << 1;
                ys[0] = 0;
                ys[1] = ys[2] = blockSize;
                g.drawPolygon(xs, ys, 3);
            } else {
                blockSize = Math.min(getWidth(), BasicSplitPaneDivider.access$000(this$0));
                xs[0] = xs[2] = blockSize;
                xs[1] = 0;
                ys[0] = 0;
                ys[1] = blockSize;
                ys[2] = blockSize << 1;
            }
            g.fillPolygon(xs, ys, 3);
        }
    }
    
    public boolean isFocusTraversable() {
        return false;
    }
}
