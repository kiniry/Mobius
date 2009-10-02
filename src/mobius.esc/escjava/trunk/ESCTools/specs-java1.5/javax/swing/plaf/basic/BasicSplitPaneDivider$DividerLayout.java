package javax.swing.plaf.basic;

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import java.beans.*;

public class BasicSplitPaneDivider$DividerLayout implements LayoutManager {
    /*synthetic*/ final BasicSplitPaneDivider this$0;
    
    protected BasicSplitPaneDivider$DividerLayout(/*synthetic*/ final BasicSplitPaneDivider this$0) {
        this.this$0 = this$0;
        
    }
    
    public void layoutContainer(Container c) {
        if (this$0.leftButton != null && this$0.rightButton != null && c == this$0) {
            if (this$0.splitPane.isOneTouchExpandable()) {
                Insets insets = this$0.getInsets();
                if (this$0.orientation == JSplitPane.VERTICAL_SPLIT) {
                    int extraX = (insets != null) ? insets.left : 0;
                    int blockSize = this$0.getHeight();
                    if (insets != null) {
                        blockSize -= (insets.top + insets.bottom);
                        blockSize = Math.max(blockSize, 0);
                    }
                    blockSize = Math.min(blockSize, BasicSplitPaneDivider.access$000(this$0));
                    int y = (c.getSize().height - blockSize) / 2;
                    if (!BasicSplitPaneDivider.access$100(this$0)) {
                        y = (insets != null) ? insets.top : 0;
                        extraX = 0;
                    }
                    this$0.leftButton.setBounds(extraX + BasicSplitPaneDivider.access$200(this$0), y, blockSize * 2, blockSize);
                    this$0.rightButton.setBounds(extraX + BasicSplitPaneDivider.access$200(this$0) + BasicSplitPaneDivider.access$000(this$0) * 2, y, blockSize * 2, blockSize);
                } else {
                    int extraY = (insets != null) ? insets.top : 0;
                    int blockSize = this$0.getWidth();
                    if (insets != null) {
                        blockSize -= (insets.left + insets.right);
                        blockSize = Math.max(blockSize, 0);
                    }
                    blockSize = Math.min(blockSize, BasicSplitPaneDivider.access$000(this$0));
                    int x = (c.getSize().width - blockSize) / 2;
                    if (!BasicSplitPaneDivider.access$100(this$0)) {
                        x = (insets != null) ? insets.left : 0;
                        extraY = 0;
                    }
                    this$0.leftButton.setBounds(x, extraY + BasicSplitPaneDivider.access$200(this$0), blockSize, blockSize * 2);
                    this$0.rightButton.setBounds(x, extraY + BasicSplitPaneDivider.access$200(this$0) + BasicSplitPaneDivider.access$000(this$0) * 2, blockSize, blockSize * 2);
                }
            } else {
                this$0.leftButton.setBounds(-5, -5, 1, 1);
                this$0.rightButton.setBounds(-5, -5, 1, 1);
            }
        }
    }
    
    public Dimension minimumLayoutSize(Container c) {
        if (c != this$0 || this$0.splitPane == null) {
            return new Dimension(0, 0);
        }
        Dimension buttonMinSize = null;
        if (this$0.splitPane.isOneTouchExpandable() && this$0.leftButton != null) {
            buttonMinSize = this$0.leftButton.getMinimumSize();
        }
        Insets insets = this$0.getInsets();
        int width = this$0.getDividerSize();
        int height = width;
        if (this$0.orientation == JSplitPane.VERTICAL_SPLIT) {
            if (buttonMinSize != null) {
                int size = buttonMinSize.height;
                if (insets != null) {
                    size += insets.top + insets.bottom;
                }
                height = Math.max(height, size);
            }
            width = 1;
        } else {
            if (buttonMinSize != null) {
                int size = buttonMinSize.width;
                if (insets != null) {
                    size += insets.left + insets.right;
                }
                width = Math.max(width, size);
            }
            height = 1;
        }
        return new Dimension(width, height);
    }
    
    public Dimension preferredLayoutSize(Container c) {
        return minimumLayoutSize(c);
    }
    
    public void removeLayoutComponent(Component c) {
    }
    
    public void addLayoutComponent(String string, Component c) {
    }
}
