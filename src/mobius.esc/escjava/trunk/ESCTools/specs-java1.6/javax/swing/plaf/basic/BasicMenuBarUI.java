package javax.swing.plaf.basic;

import sun.swing.DefaultLookup;
import javax.swing.*;
import javax.swing.event.*;
import java.awt.Dimension;
import java.awt.event.*;
import javax.swing.border.*;
import javax.swing.plaf.*;

public class BasicMenuBarUI extends MenuBarUI {
    {
    }
    
    public BasicMenuBarUI() {
        
    }
    protected JMenuBar menuBar = null;
    protected ContainerListener containerListener;
    protected ChangeListener changeListener;
    private BasicMenuBarUI$Handler handler;
    
    public static ComponentUI createUI(JComponent x) {
        return new BasicMenuBarUI();
    }
    
    static void loadActionMap(LazyActionMap map) {
        map.put(new BasicMenuBarUI$Actions("takeFocus"));
    }
    
    public void installUI(JComponent c) {
        menuBar = (JMenuBar)(JMenuBar)c;
        installDefaults();
        installListeners();
        installKeyboardActions();
    }
    
    protected void installDefaults() {
        if (menuBar.getLayout() == null || menuBar.getLayout() instanceof UIResource) {
            menuBar.setLayout(new DefaultMenuLayout(menuBar, BoxLayout.LINE_AXIS));
        }
        LookAndFeel.installProperty(menuBar, "opaque", Boolean.TRUE);
        LookAndFeel.installBorder(menuBar, "MenuBar.border");
        LookAndFeel.installColorsAndFont(menuBar, "MenuBar.background", "MenuBar.foreground", "MenuBar.font");
    }
    
    protected void installListeners() {
        containerListener = createContainerListener();
        changeListener = createChangeListener();
        for (int i = 0; i < menuBar.getMenuCount(); i++) {
            JMenu menu = menuBar.getMenu(i);
            if (menu != null) menu.getModel().addChangeListener(changeListener);
        }
        menuBar.addContainerListener(containerListener);
    }
    
    protected void installKeyboardActions() {
        InputMap inputMap = getInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW);
        SwingUtilities.replaceUIInputMap(menuBar, JComponent.WHEN_IN_FOCUSED_WINDOW, inputMap);
        LazyActionMap.installLazyActionMap(menuBar, BasicMenuBarUI.class, "MenuBar.actionMap");
    }
    
    InputMap getInputMap(int condition) {
        if (condition == JComponent.WHEN_IN_FOCUSED_WINDOW) {
            Object[] bindings = (Object[])(Object[])DefaultLookup.get(menuBar, this, "MenuBar.windowBindings");
            if (bindings != null) {
                return LookAndFeel.makeComponentInputMap(menuBar, bindings);
            }
        }
        return null;
    }
    
    public void uninstallUI(JComponent c) {
        uninstallDefaults();
        uninstallListeners();
        uninstallKeyboardActions();
        menuBar = null;
    }
    
    protected void uninstallDefaults() {
        if (menuBar != null) {
            LookAndFeel.uninstallBorder(menuBar);
        }
    }
    
    protected void uninstallListeners() {
        menuBar.removeContainerListener(containerListener);
        for (int i = 0; i < menuBar.getMenuCount(); i++) {
            JMenu menu = menuBar.getMenu(i);
            if (menu != null) menu.getModel().removeChangeListener(changeListener);
        }
        containerListener = null;
        changeListener = null;
        handler = null;
    }
    
    protected void uninstallKeyboardActions() {
        SwingUtilities.replaceUIInputMap(menuBar, JComponent.WHEN_IN_FOCUSED_WINDOW, null);
        SwingUtilities.replaceUIActionMap(menuBar, null);
    }
    
    protected ContainerListener createContainerListener() {
        return getHandler();
    }
    
    protected ChangeListener createChangeListener() {
        return getHandler();
    }
    
    private BasicMenuBarUI$Handler getHandler() {
        if (handler == null) {
            handler = new BasicMenuBarUI$Handler(this, null);
        }
        return handler;
    }
    
    public Dimension getMinimumSize(JComponent c) {
        return null;
    }
    
    public Dimension getMaximumSize(JComponent c) {
        return null;
    }
    {
    }
    {
    }
}
