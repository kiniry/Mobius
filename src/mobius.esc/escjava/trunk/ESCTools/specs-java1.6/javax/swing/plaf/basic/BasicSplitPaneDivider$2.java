package javax.swing.plaf.basic;

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.border.Border;
import java.beans.*;

class BasicSplitPaneDivider$2 extends JButton {
    /*synthetic*/ final BasicSplitPaneDivider this$0;
    
    BasicSplitPaneDivider$2(/*synthetic*/ final BasicSplitPaneDivider this$0) {
        this.this$0 = this$0;
        
    }
    
    public void setBorder(Border border) {
    }
    
    public void paint(Graphics g) {
        if (this$0.splitPane != null) {
            int[] xs = new int[3];
            int[] ys = new int[3];
            int blockSize;
            g.setColor(this.getBackground());
            g.fillRect(0, 0, this.getWidth(), this.getHeight());
            if (this$0.orientation == JSplitPane.VERTICAL_SPLIT) {
                blockSize = Math.min(getHeight(), BasicSplitPaneDivider.access$000(this$0));
                xs[0] = blockSize;
                xs[1] = blockSize << 1;
                xs[2] = 0;
                ys[0] = blockSize;
                ys[1] = ys[2] = 0;
            } else {
                blockSize = Math.min(getWidth(), BasicSplitPaneDivider.access$000(this$0));
                xs[0] = xs[2] = 0;
                xs[1] = blockSize;
                ys[0] = 0;
                ys[1] = blockSize;
                ys[2] = blockSize << 1;
            }
            g.setColor(Color.black);
            g.fillPolygon(xs, ys, 3);
        }
    }
    
    public boolean isFocusTraversable() {
        return false;
    }
}
