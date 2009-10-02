package javax.swing.plaf.basic;

import java.awt.event.ActionEvent;
import java.awt.KeyboardFocusManager;
import java.awt.Component;
import java.awt.Point;
import java.awt.Rectangle;
import javax.swing.*;
import javax.swing.plaf.*;
import sun.swing.UIAction;

class BasicRootPaneUI$Actions extends UIAction {
    public static final String PRESS = "press";
    public static final String RELEASE = "release";
    public static final String POST_POPUP = "postPopup";
    
    BasicRootPaneUI$Actions(String name) {
        super(name);
    }
    
    public void actionPerformed(ActionEvent evt) {
        JRootPane root = (JRootPane)(JRootPane)evt.getSource();
        JButton owner = root.getDefaultButton();
        String key = getName();
        if (key == POST_POPUP) {
            Component c = KeyboardFocusManager.getCurrentKeyboardFocusManager().getFocusOwner();
            if (c instanceof JComponent) {
                JComponent src = (JComponent)(JComponent)c;
                JPopupMenu jpm = src.getComponentPopupMenu();
                if (jpm != null) {
                    Point pt = src.getPopupLocation(null);
                    if (pt == null) {
                        Rectangle vis = src.getVisibleRect();
                        pt = new Point(vis.x + vis.width / 2, vis.y + vis.height / 2);
                    }
                    jpm.show(c, pt.x, pt.y);
                }
            }
        } else if (owner != null && SwingUtilities.getRootPane(owner) == root) {
            if (key == PRESS) {
                owner.doClick(20);
            }
        }
    }
    
    public boolean isEnabled(Object sender) {
        String key = getName();
        if (key == POST_POPUP) {
            MenuElement[] elems = MenuSelectionManager.defaultManager().getSelectedPath();
            if (elems != null && elems.length != 0) {
                return false;
            }
            Component c = KeyboardFocusManager.getCurrentKeyboardFocusManager().getFocusOwner();
            if (c instanceof JComponent) {
                JComponent src = (JComponent)(JComponent)c;
                return src.getComponentPopupMenu() != null;
            }
            return false;
        }
        if (sender != null && sender instanceof JRootPane) {
            JButton owner = ((JRootPane)(JRootPane)sender).getDefaultButton();
            return (owner != null && owner.getModel().isEnabled());
        }
        return true;
    }
}
