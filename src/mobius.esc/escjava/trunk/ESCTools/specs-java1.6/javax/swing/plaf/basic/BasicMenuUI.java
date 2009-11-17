package javax.swing.plaf.basic;

import sun.swing.DefaultLookup;
import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.border.*;

public class BasicMenuUI extends BasicMenuItemUI {
    
    /*synthetic*/ static void access$300(BasicMenuUI x0) {
        x0.updateDefaultBackgroundColor();
    }
    
    /*synthetic*/ static void access$200(MenuElement[] x0, MenuElement x1) {
        appendPath(x0, x1);
    }
    
    /*synthetic*/ static boolean access$100() {
        return crossMenuMnemonic;
    }
    {
    }
    
    public BasicMenuUI() {
        
    }
    protected ChangeListener changeListener;
    protected PropertyChangeListener propertyChangeListener;
    protected MenuListener menuListener;
    private int lastMnemonic = 0;
    private InputMap selectedWindowInputMap;
    private static final boolean TRACE = false;
    private static final boolean VERBOSE = false;
    private static final boolean DEBUG = false;
    private static boolean crossMenuMnemonic = true;
    
    public static ComponentUI createUI(JComponent x) {
        return new BasicMenuUI();
    }
    
    static void loadActionMap(LazyActionMap map) {
        BasicMenuItemUI.loadActionMap(map);
        map.put(new BasicMenuUI$Actions("selectMenu", null, true));
    }
    
    protected void installDefaults() {
        super.installDefaults();
        updateDefaultBackgroundColor();
        ((JMenu)(JMenu)menuItem).setDelay(200);
        crossMenuMnemonic = UIManager.getBoolean("Menu.crossMenuMnemonic");
    }
    
    protected String getPropertyPrefix() {
        return "Menu";
    }
    
    protected void installListeners() {
        super.installListeners();
        if (changeListener == null) changeListener = createChangeListener(menuItem);
        if (changeListener != null) menuItem.addChangeListener(changeListener);
        if (propertyChangeListener == null) propertyChangeListener = createPropertyChangeListener(menuItem);
        if (propertyChangeListener != null) menuItem.addPropertyChangeListener(propertyChangeListener);
        if (menuListener == null) menuListener = createMenuListener(menuItem);
        if (menuListener != null) ((JMenu)(JMenu)menuItem).addMenuListener(menuListener);
    }
    
    protected void installKeyboardActions() {
        super.installKeyboardActions();
        updateMnemonicBinding();
    }
    
    void installLazyActionMap() {
        LazyActionMap.installLazyActionMap(menuItem, BasicMenuUI.class, getPropertyPrefix() + ".actionMap");
    }
    
    void updateMnemonicBinding() {
        int mnemonic = menuItem.getModel().getMnemonic();
        int[] shortcutKeys = (int[])(int[])DefaultLookup.get(menuItem, this, "Menu.shortcutKeys");
        if (shortcutKeys == null) {
            shortcutKeys = new int[]{KeyEvent.ALT_MASK};
        }
        if (mnemonic == lastMnemonic) {
            return;
        }
        InputMap windowInputMap = SwingUtilities.getUIInputMap(menuItem, JComponent.WHEN_IN_FOCUSED_WINDOW);
        if (lastMnemonic != 0 && windowInputMap != null) {
            for (int i = 0; i < shortcutKeys.length; i++) {
                windowInputMap.remove(KeyStroke.getKeyStroke(lastMnemonic, shortcutKeys[i], false));
            }
        }
        if (mnemonic != 0) {
            if (windowInputMap == null) {
                windowInputMap = createInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW);
                SwingUtilities.replaceUIInputMap(menuItem, JComponent.WHEN_IN_FOCUSED_WINDOW, windowInputMap);
            }
            for (int i = 0; i < shortcutKeys.length; i++) {
                windowInputMap.put(KeyStroke.getKeyStroke(mnemonic, shortcutKeys[i], false), "selectMenu");
            }
        }
        lastMnemonic = mnemonic;
    }
    
    protected void uninstallKeyboardActions() {
        super.uninstallKeyboardActions();
        lastMnemonic = 0;
    }
    
    protected MouseInputListener createMouseInputListener(JComponent c) {
        return getHandler();
    }
    
    protected MenuListener createMenuListener(JComponent c) {
        return null;
    }
    
    protected ChangeListener createChangeListener(JComponent c) {
        return null;
    }
    
    protected PropertyChangeListener createPropertyChangeListener(JComponent c) {
        return getHandler();
    }
    
    BasicMenuItemUI$Handler getHandler() {
        if (handler == null) {
            handler = new BasicMenuUI$Handler(this, null);
        }
        return handler;
    }
    
    protected void uninstallDefaults() {
        menuItem.setArmed(false);
        menuItem.setSelected(false);
        menuItem.resetKeyboardActions();
        super.uninstallDefaults();
    }
    
    protected void uninstallListeners() {
        super.uninstallListeners();
        if (changeListener != null) menuItem.removeChangeListener(changeListener);
        if (propertyChangeListener != null) menuItem.removePropertyChangeListener(propertyChangeListener);
        if (menuListener != null) ((JMenu)(JMenu)menuItem).removeMenuListener(menuListener);
        changeListener = null;
        propertyChangeListener = null;
        menuListener = null;
        handler = null;
    }
    
    protected MenuDragMouseListener createMenuDragMouseListener(JComponent c) {
        return getHandler();
    }
    
    protected MenuKeyListener createMenuKeyListener(JComponent c) {
        return (MenuKeyListener)(MenuKeyListener)getHandler();
    }
    
    public Dimension getMaximumSize(JComponent c) {
        if (((JMenu)(JMenu)menuItem).isTopLevelMenu() == true) {
            Dimension d = c.getPreferredSize();
            return new Dimension(d.width, Short.MAX_VALUE);
        }
        return null;
    }
    
    protected void setupPostTimer(JMenu menu) {
        Timer timer = new Timer(menu.getDelay(), new BasicMenuUI$Actions("selectMenu", menu, false));
        timer.setRepeats(false);
        timer.start();
    }
    
    private static void appendPath(MenuElement[] path, MenuElement elem) {
        MenuElement[] newPath = new MenuElement[path.length + 1];
        System.arraycopy(path, 0, newPath, 0, path.length);
        newPath[path.length] = elem;
        MenuSelectionManager.defaultManager().setSelectedPath(newPath);
    }
    {
    }
    
    private void updateDefaultBackgroundColor() {
        if (!UIManager.getBoolean("Menu.useMenuBarBackgroundForTopLevel")) {
            return;
        }
        JMenu menu = (JMenu)(JMenu)menuItem;
        if (menu.getBackground() instanceof UIResource) {
            if (menu.isTopLevelMenu()) {
                menu.setBackground(UIManager.getColor("MenuBar.background"));
            } else {
                menu.setBackground(UIManager.getColor(getPropertyPrefix() + ".background"));
            }
        }
    }
    {
    }
    {
    }
    {
    }
}
