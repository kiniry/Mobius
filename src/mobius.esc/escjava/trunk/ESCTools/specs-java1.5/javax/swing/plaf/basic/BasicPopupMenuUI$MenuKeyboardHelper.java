package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.plaf.basic.*;
import javax.swing.border.*;
import java.awt.Component;
import java.awt.KeyboardFocusManager;
import java.awt.Window;
import java.awt.event.*;
import java.util.*;

class BasicPopupMenuUI$MenuKeyboardHelper implements ChangeListener, KeyListener {
    
    /*synthetic*/ static Component access$402(BasicPopupMenuUI$MenuKeyboardHelper x0, Component x1) {
        return x0.lastFocused = x1;
    }
    
    /*synthetic*/ BasicPopupMenuUI$MenuKeyboardHelper(javax.swing.plaf.basic.BasicPopupMenuUI$1 x0) {
        this();
    }
    
    private BasicPopupMenuUI$MenuKeyboardHelper() {
        
    }
    private Component lastFocused = null;
    private MenuElement[] lastPathSelected = new MenuElement[0];
    private JPopupMenu lastPopup;
    private JRootPane invokerRootPane;
    private ActionMap menuActionMap = BasicPopupMenuUI.getActionMap();
    private InputMap menuInputMap;
    private boolean focusTraversalKeysEnabled;
    private boolean receivedKeyPressed = false;
    
    void removeItems() {
        if (lastFocused != null) {
            if (!lastFocused.requestFocusInWindow()) {
                Window cfw = KeyboardFocusManager.getCurrentKeyboardFocusManager().getFocusedWindow();
                if (cfw != null && "###focusableSwingPopup###".equals(cfw.getName())) {
                    lastFocused.requestFocus();
                }
            }
            lastFocused = null;
        }
        if (invokerRootPane != null) {
            invokerRootPane.removeKeyListener(BasicPopupMenuUI.menuKeyboardHelper);
            invokerRootPane.setFocusTraversalKeysEnabled(focusTraversalKeysEnabled);
            removeUIInputMap(invokerRootPane, menuInputMap);
            removeUIActionMap(invokerRootPane, menuActionMap);
            invokerRootPane = null;
        }
        receivedKeyPressed = false;
    }
    private FocusListener rootPaneFocusListener = new BasicPopupMenuUI$MenuKeyboardHelper$1(this);
    
    JPopupMenu getActivePopup(MenuElement[] path) {
        for (int i = path.length - 1; i >= 0; i--) {
            MenuElement elem = path[i];
            if (elem instanceof JPopupMenu) {
                return (JPopupMenu)(JPopupMenu)elem;
            }
        }
        return null;
    }
    
    void addUIInputMap(JComponent c, InputMap map) {
        InputMap lastNonUI = null;
        InputMap parent = c.getInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW);
        while (parent != null && !(parent instanceof UIResource)) {
            lastNonUI = parent;
            parent = parent.getParent();
        }
        if (lastNonUI == null) {
            c.setInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW, map);
        } else {
            lastNonUI.setParent(map);
        }
        map.setParent(parent);
    }
    
    void addUIActionMap(JComponent c, ActionMap map) {
        ActionMap lastNonUI = null;
        ActionMap parent = c.getActionMap();
        while (parent != null && !(parent instanceof UIResource)) {
            lastNonUI = parent;
            parent = parent.getParent();
        }
        if (lastNonUI == null) {
            c.setActionMap(map);
        } else {
            lastNonUI.setParent(map);
        }
        map.setParent(parent);
    }
    
    void removeUIInputMap(JComponent c, InputMap map) {
        InputMap im = null;
        InputMap parent = c.getInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW);
        while (parent != null) {
            if (parent == map) {
                if (im == null) {
                    c.setInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW, map.getParent());
                } else {
                    im.setParent(map.getParent());
                }
                break;
            }
            im = parent;
            parent = parent.getParent();
        }
    }
    
    void removeUIActionMap(JComponent c, ActionMap map) {
        ActionMap im = null;
        ActionMap parent = c.getActionMap();
        while (parent != null) {
            if (parent == map) {
                if (im == null) {
                    c.setActionMap(map.getParent());
                } else {
                    im.setParent(map.getParent());
                }
                break;
            }
            im = parent;
            parent = parent.getParent();
        }
    }
    
    public void stateChanged(ChangeEvent ev) {
        if (!(UIManager.getLookAndFeel() instanceof BasicLookAndFeel)) {
            MenuSelectionManager msm = MenuSelectionManager.defaultManager();
            msm.removeChangeListener(this);
            BasicPopupMenuUI.menuKeyboardHelperInstalled = false;
            return;
        }
        MenuSelectionManager msm = (MenuSelectionManager)(MenuSelectionManager)ev.getSource();
        MenuElement[] p = msm.getSelectedPath();
        JPopupMenu popup = getActivePopup(p);
        if (popup != null && !popup.isFocusable()) {
            return;
        }
        if (lastPathSelected.length != 0 && p.length != 0) {
            if (!BasicPopupMenuUI.access$500(p[0], lastPathSelected[0])) {
                removeItems();
                lastPathSelected = new MenuElement[0];
            }
        }
        if (lastPathSelected.length == 0 && p.length > 0) {
            JComponent invoker;
            if (popup == null) {
                if (p.length == 2 && p[0] instanceof JMenuBar && p[1] instanceof JMenu) {
                    invoker = (JComponent)(JComponent)p[1];
                    popup = ((JMenu)(JMenu)invoker).getPopupMenu();
                } else {
                    return;
                }
            } else {
                Component c = popup.getInvoker();
                if (c instanceof JFrame) {
                    invoker = ((JFrame)(JFrame)c).getRootPane();
                } else if (c instanceof JApplet) {
                    invoker = ((JApplet)(JApplet)c).getRootPane();
                } else {
                    while (!(c instanceof JComponent)) {
                        if (c == null) {
                            return;
                        }
                        c = c.getParent();
                    }
                    invoker = (JComponent)(JComponent)c;
                }
            }
            lastFocused = KeyboardFocusManager.getCurrentKeyboardFocusManager().getFocusOwner();
            invokerRootPane = SwingUtilities.getRootPane(invoker);
            if (invokerRootPane != null) {
                invokerRootPane.addFocusListener(rootPaneFocusListener);
                invokerRootPane.requestFocus(true);
                invokerRootPane.addKeyListener(BasicPopupMenuUI.menuKeyboardHelper);
                focusTraversalKeysEnabled = invokerRootPane.getFocusTraversalKeysEnabled();
                invokerRootPane.setFocusTraversalKeysEnabled(false);
                menuInputMap = BasicPopupMenuUI.getInputMap(popup, invokerRootPane);
                addUIInputMap(invokerRootPane, menuInputMap);
                addUIActionMap(invokerRootPane, menuActionMap);
            }
        } else if (lastPathSelected.length != 0 && p.length == 0) {
            removeItems();
        } else {
            if (popup != lastPopup) {
                receivedKeyPressed = false;
            }
        }
        lastPathSelected = p;
        lastPopup = popup;
    }
    
    public void keyPressed(KeyEvent ev) {
        receivedKeyPressed = true;
        MenuSelectionManager.defaultManager().processKeyEvent(ev);
    }
    
    public void keyReleased(KeyEvent ev) {
        if (receivedKeyPressed) {
            receivedKeyPressed = false;
            MenuSelectionManager.defaultManager().processKeyEvent(ev);
        }
    }
    
    public void keyTyped(KeyEvent ev) {
        if (receivedKeyPressed) {
            MenuSelectionManager.defaultManager().processKeyEvent(ev);
        }
    }
}
