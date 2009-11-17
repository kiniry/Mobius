package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.plaf.UIResource;
import java.awt.Container;
import java.awt.Dimension;

public class DefaultMenuLayout extends BoxLayout implements UIResource {
    
    public DefaultMenuLayout(Container target, int axis) {
        super(target, axis);
    }
    
    public Dimension preferredLayoutSize(Container target) {
        if (target instanceof JPopupMenu) {
            ((JPopupMenu)(JPopupMenu)target).putClientProperty(BasicMenuItemUI.MAX_TEXT_WIDTH, null);
            ((JPopupMenu)(JPopupMenu)target).putClientProperty(BasicMenuItemUI.MAX_ACC_WIDTH, null);
        }
        return super.preferredLayoutSize(target);
    }
}
