package javax.swing.plaf.basic;

import sun.swing.DefaultLookup;
import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.ComponentInputMapUIResource;

public class BasicButtonListener implements MouseListener, MouseMotionListener, FocusListener, ChangeListener, PropertyChangeListener {
    private long lastPressedTimestamp = -1;
    private boolean shouldDiscardRelease = false;
    
    static void loadActionMap(LazyActionMap map) {
        map.put(new BasicButtonListener$Actions("pressed"));
        map.put(new BasicButtonListener$Actions("released"));
    }
    
    public BasicButtonListener(AbstractButton b) {
        
    }
    
    public void propertyChange(PropertyChangeEvent e) {
        String prop = e.getPropertyName();
        if (prop == AbstractButton.MNEMONIC_CHANGED_PROPERTY) {
            updateMnemonicBinding((AbstractButton)(AbstractButton)e.getSource());
        } else if (prop == AbstractButton.CONTENT_AREA_FILLED_CHANGED_PROPERTY) {
            checkOpacity((AbstractButton)(AbstractButton)e.getSource());
        } else if (prop == AbstractButton.TEXT_CHANGED_PROPERTY || "font" == prop || "foreground" == prop) {
            AbstractButton b = (AbstractButton)(AbstractButton)e.getSource();
            BasicHTML.updateRenderer(b, b.getText());
        }
    }
    
    protected void checkOpacity(AbstractButton b) {
        b.setOpaque(b.isContentAreaFilled());
    }
    
    public void installKeyboardActions(JComponent c) {
        AbstractButton b = (AbstractButton)(AbstractButton)c;
        updateMnemonicBinding(b);
        LazyActionMap.installLazyActionMap(c, BasicButtonListener.class, "Button.actionMap");
        InputMap km = getInputMap(JComponent.WHEN_FOCUSED, c);
        SwingUtilities.replaceUIInputMap(c, JComponent.WHEN_FOCUSED, km);
    }
    
    public void uninstallKeyboardActions(JComponent c) {
        SwingUtilities.replaceUIInputMap(c, JComponent.WHEN_IN_FOCUSED_WINDOW, null);
        SwingUtilities.replaceUIInputMap(c, JComponent.WHEN_FOCUSED, null);
        SwingUtilities.replaceUIActionMap(c, null);
    }
    
    InputMap getInputMap(int condition, JComponent c) {
        if (condition == JComponent.WHEN_FOCUSED) {
            BasicButtonUI ui = (BasicButtonUI)(BasicButtonUI)BasicLookAndFeel.getUIOfType(((AbstractButton)(AbstractButton)c).getUI(), BasicButtonUI.class);
            if (ui != null) {
                return (InputMap)(InputMap)DefaultLookup.get(c, ui, ui.getPropertyPrefix() + "focusInputMap");
            }
        }
        return null;
    }
    
    void updateMnemonicBinding(AbstractButton b) {
        int m = b.getMnemonic();
        if (m != 0) {
            InputMap map = SwingUtilities.getUIInputMap(b, JComponent.WHEN_IN_FOCUSED_WINDOW);
            if (map == null) {
                map = new ComponentInputMapUIResource(b);
                SwingUtilities.replaceUIInputMap(b, JComponent.WHEN_IN_FOCUSED_WINDOW, map);
            }
            map.clear();
            map.put(KeyStroke.getKeyStroke(m, InputEvent.ALT_MASK, false), "pressed");
            map.put(KeyStroke.getKeyStroke(m, InputEvent.ALT_MASK, true), "released");
            map.put(KeyStroke.getKeyStroke(m, 0, true), "released");
        } else {
            InputMap map = SwingUtilities.getUIInputMap(b, JComponent.WHEN_IN_FOCUSED_WINDOW);
            if (map != null) {
                map.clear();
            }
        }
    }
    
    public void stateChanged(ChangeEvent e) {
        AbstractButton b = (AbstractButton)(AbstractButton)e.getSource();
        b.repaint();
    }
    
    public void focusGained(FocusEvent e) {
        AbstractButton b = (AbstractButton)(AbstractButton)e.getSource();
        if (b instanceof JButton && ((JButton)(JButton)b).isDefaultCapable()) {
            JRootPane root = b.getRootPane();
            if (root != null) {
                BasicButtonUI ui = (BasicButtonUI)(BasicButtonUI)BasicLookAndFeel.getUIOfType(((AbstractButton)b).getUI(), BasicButtonUI.class);
                if (ui != null && DefaultLookup.getBoolean(b, ui, ui.getPropertyPrefix() + "defaultButtonFollowsFocus", true)) {
                    root.putClientProperty("temporaryDefaultButton", b);
                    root.setDefaultButton((JButton)(JButton)b);
                    root.putClientProperty("temporaryDefaultButton", null);
                }
            }
        }
        b.repaint();
    }
    
    public void focusLost(FocusEvent e) {
        AbstractButton b = (AbstractButton)(AbstractButton)e.getSource();
        JRootPane root = b.getRootPane();
        if (root != null) {
            JButton initialDefault = (JButton)(JButton)root.getClientProperty("initialDefaultButton");
            if (b != initialDefault) {
                BasicButtonUI ui = (BasicButtonUI)(BasicButtonUI)BasicLookAndFeel.getUIOfType(((AbstractButton)b).getUI(), BasicButtonUI.class);
                if (ui != null && DefaultLookup.getBoolean(b, ui, ui.getPropertyPrefix() + "defaultButtonFollowsFocus", true)) {
                    root.setDefaultButton(initialDefault);
                }
            }
        }
        ButtonModel model = b.getModel();
        model.setArmed(false);
        model.setPressed(false);
        b.repaint();
    }
    
    public void mouseMoved(MouseEvent e) {
    }
    
    public void mouseDragged(MouseEvent e) {
    }
    
    public void mouseClicked(MouseEvent e) {
    }
    
    public void mousePressed(MouseEvent e) {
        if (SwingUtilities.isLeftMouseButton(e)) {
            AbstractButton b = (AbstractButton)(AbstractButton)e.getSource();
            if (b.contains(e.getX(), e.getY())) {
                long multiClickThreshhold = b.getMultiClickThreshhold();
                long lastTime = lastPressedTimestamp;
                long currentTime = lastPressedTimestamp = e.getWhen();
                if (lastTime != -1 && currentTime - lastTime < multiClickThreshhold) {
                    shouldDiscardRelease = true;
                    return;
                }
                ButtonModel model = b.getModel();
                if (!model.isEnabled()) {
                    return;
                }
                if (!model.isArmed()) {
                    model.setArmed(true);
                }
                model.setPressed(true);
                if (!b.hasFocus() && b.isRequestFocusEnabled()) {
                    b.requestFocus();
                }
            }
        }
    }
    {
    }
    
    public void mouseReleased(MouseEvent e) {
        if (SwingUtilities.isLeftMouseButton(e)) {
            if (shouldDiscardRelease) {
                shouldDiscardRelease = false;
                return;
            }
            AbstractButton b = (AbstractButton)(AbstractButton)e.getSource();
            ButtonModel model = b.getModel();
            model.setPressed(false);
            model.setArmed(false);
        }
    }
    {
    }
    
    public void mouseEntered(MouseEvent e) {
        AbstractButton b = (AbstractButton)(AbstractButton)e.getSource();
        ButtonModel model = b.getModel();
        if (b.isRolloverEnabled() && !SwingUtilities.isLeftMouseButton(e)) {
            model.setRollover(true);
        }
        if (model.isPressed()) model.setArmed(true);
    }
    {
    }
    
    public void mouseExited(MouseEvent e) {
        AbstractButton b = (AbstractButton)(AbstractButton)e.getSource();
        ButtonModel model = b.getModel();
        if (b.isRolloverEnabled()) {
            model.setRollover(false);
        }
        model.setArmed(false);
    }
    {
    }
    {
    }
}
