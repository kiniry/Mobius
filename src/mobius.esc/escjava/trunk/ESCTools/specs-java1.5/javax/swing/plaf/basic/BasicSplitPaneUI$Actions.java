package javax.swing.plaf.basic;

import sun.swing.UIAction;
import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.util.*;

class BasicSplitPaneUI$Actions extends UIAction {
    private static final String NEGATIVE_INCREMENT = "negativeIncrement";
    private static final String POSITIVE_INCREMENT = "positiveIncrement";
    private static final String SELECT_MIN = "selectMin";
    private static final String SELECT_MAX = "selectMax";
    private static final String START_RESIZE = "startResize";
    private static final String TOGGLE_FOCUS = "toggleFocus";
    private static final String FOCUS_OUT_FORWARD = "focusOutForward";
    private static final String FOCUS_OUT_BACKWARD = "focusOutBackward";
    
    BasicSplitPaneUI$Actions(String key) {
        super(key);
    }
    
    public void actionPerformed(ActionEvent ev) {
        JSplitPane splitPane = (JSplitPane)(JSplitPane)ev.getSource();
        BasicSplitPaneUI ui = (BasicSplitPaneUI)(BasicSplitPaneUI)BasicLookAndFeel.getUIOfType(splitPane.getUI(), BasicSplitPaneUI.class);
        if (ui == null) {
            return;
        }
        String key = getName();
        if (key == NEGATIVE_INCREMENT) {
            if (BasicSplitPaneUI.access$200(ui)) {
                splitPane.setDividerLocation(Math.max(0, ui.getDividerLocation(splitPane) - ui.getKeyboardMoveIncrement()));
            }
        } else if (key == POSITIVE_INCREMENT) {
            if (BasicSplitPaneUI.access$200(ui)) {
                splitPane.setDividerLocation(ui.getDividerLocation(splitPane) + ui.getKeyboardMoveIncrement());
            }
        } else if (key == SELECT_MIN) {
            if (BasicSplitPaneUI.access$200(ui)) {
                splitPane.setDividerLocation(0);
            }
        } else if (key == SELECT_MAX) {
            if (BasicSplitPaneUI.access$200(ui)) {
                Insets insets = splitPane.getInsets();
                int bottomI = (insets != null) ? insets.bottom : 0;
                int rightI = (insets != null) ? insets.right : 0;
                if (BasicSplitPaneUI.access$300(ui) == JSplitPane.VERTICAL_SPLIT) {
                    splitPane.setDividerLocation(splitPane.getHeight() - bottomI);
                } else {
                    splitPane.setDividerLocation(splitPane.getWidth() - rightI);
                }
            }
        } else if (key == START_RESIZE) {
            if (!BasicSplitPaneUI.access$200(ui)) {
                splitPane.requestFocus();
            } else {
                JSplitPane parentSplitPane = (JSplitPane)(JSplitPane)SwingUtilities.getAncestorOfClass(JSplitPane.class, splitPane);
                if (parentSplitPane != null) {
                    parentSplitPane.requestFocus();
                }
            }
        } else if (key == TOGGLE_FOCUS) {
            toggleFocus(splitPane);
        } else if (key == FOCUS_OUT_FORWARD) {
            moveFocus(splitPane, 1);
        } else if (key == FOCUS_OUT_BACKWARD) {
            moveFocus(splitPane, -1);
        }
    }
    
    private void moveFocus(JSplitPane splitPane, int direction) {
        Container rootAncestor = splitPane.getFocusCycleRootAncestor();
        FocusTraversalPolicy policy = rootAncestor.getFocusTraversalPolicy();
        Component focusOn = (direction > 0) ? policy.getComponentAfter(rootAncestor, splitPane) : policy.getComponentBefore(rootAncestor, splitPane);
        HashSet focusFrom = new HashSet();
        if (splitPane.isAncestorOf(focusOn)) {
            do {
                focusFrom.add(focusOn);
                rootAncestor = focusOn.getFocusCycleRootAncestor();
                policy = rootAncestor.getFocusTraversalPolicy();
                focusOn = (direction > 0) ? policy.getComponentAfter(rootAncestor, focusOn) : policy.getComponentBefore(rootAncestor, focusOn);
            }             while (splitPane.isAncestorOf(focusOn) && !focusFrom.contains(focusOn));
        }
        if (focusOn != null && !splitPane.isAncestorOf(focusOn)) {
            focusOn.requestFocus();
        }
    }
    
    private void toggleFocus(JSplitPane splitPane) {
        Component left = splitPane.getLeftComponent();
        Component right = splitPane.getRightComponent();
        KeyboardFocusManager manager = KeyboardFocusManager.getCurrentKeyboardFocusManager();
        Component focus = manager.getFocusOwner();
        Component focusOn = getNextSide(splitPane, focus);
        if (focusOn != null) {
            if (focus != null && ((SwingUtilities.isDescendingFrom(focus, left) && SwingUtilities.isDescendingFrom(focusOn, left)) || (SwingUtilities.isDescendingFrom(focus, right) && SwingUtilities.isDescendingFrom(focusOn, right)))) {
                return;
            }
            BasicLookAndFeel.compositeRequestFocus(focusOn);
        }
    }
    
    private Component getNextSide(JSplitPane splitPane, Component focus) {
        Component left = splitPane.getLeftComponent();
        Component right = splitPane.getRightComponent();
        Component next = null;
        if (focus != null && SwingUtilities.isDescendingFrom(focus, left) && right != null) {
            next = getFirstAvailableComponent(right);
            if (next != null) {
                return next;
            }
        }
        JSplitPane parentSplitPane = (JSplitPane)(JSplitPane)SwingUtilities.getAncestorOfClass(JSplitPane.class, splitPane);
        if (parentSplitPane != null) {
            next = getNextSide(parentSplitPane, focus);
        } else {
            next = getFirstAvailableComponent(left);
            if (next == null) {
                next = getFirstAvailableComponent(right);
            }
        }
        return next;
    }
    
    private Component getFirstAvailableComponent(Component c) {
        if (c != null && c instanceof JSplitPane) {
            JSplitPane sp = (JSplitPane)(JSplitPane)c;
            Component left = getFirstAvailableComponent(sp.getLeftComponent());
            if (left != null) {
                c = left;
            } else {
                c = getFirstAvailableComponent(sp.getRightComponent());
            }
        }
        return c;
    }
}
