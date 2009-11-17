package javax.swing.plaf.basic;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import javax.swing.*;
import javax.swing.plaf.*;
import sun.swing.DefaultLookup;

public class BasicRootPaneUI extends RootPaneUI implements PropertyChangeListener {
    
    public BasicRootPaneUI() {
        
    }
    private static RootPaneUI rootPaneUI = new BasicRootPaneUI();
    
    public static ComponentUI createUI(JComponent c) {
        return rootPaneUI;
    }
    
    public void installUI(JComponent c) {
        installDefaults((JRootPane)(JRootPane)c);
        installComponents((JRootPane)(JRootPane)c);
        installListeners((JRootPane)(JRootPane)c);
        installKeyboardActions((JRootPane)(JRootPane)c);
    }
    
    public void uninstallUI(JComponent c) {
        uninstallDefaults((JRootPane)(JRootPane)c);
        uninstallComponents((JRootPane)(JRootPane)c);
        uninstallListeners((JRootPane)(JRootPane)c);
        uninstallKeyboardActions((JRootPane)(JRootPane)c);
    }
    
    protected void installDefaults(JRootPane c) {
        LookAndFeel.installProperty(c, "opaque", Boolean.FALSE);
    }
    
    protected void installComponents(JRootPane root) {
    }
    
    protected void installListeners(JRootPane root) {
        root.addPropertyChangeListener(this);
    }
    
    protected void installKeyboardActions(JRootPane root) {
        InputMap km = getInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW, root);
        SwingUtilities.replaceUIInputMap(root, JComponent.WHEN_IN_FOCUSED_WINDOW, km);
        km = getInputMap(JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT, root);
        SwingUtilities.replaceUIInputMap(root, JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT, km);
        LazyActionMap.installLazyActionMap(root, BasicRootPaneUI.class, "RootPane.actionMap");
        updateDefaultButtonBindings(root);
    }
    
    protected void uninstallDefaults(JRootPane root) {
    }
    
    protected void uninstallComponents(JRootPane root) {
    }
    
    protected void uninstallListeners(JRootPane root) {
        root.removePropertyChangeListener(this);
    }
    
    protected void uninstallKeyboardActions(JRootPane root) {
        SwingUtilities.replaceUIInputMap(root, JComponent.WHEN_IN_FOCUSED_WINDOW, null);
        SwingUtilities.replaceUIActionMap(root, null);
    }
    
    InputMap getInputMap(int condition, JComponent c) {
        if (condition == JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT) {
            return (InputMap)(InputMap)DefaultLookup.get(c, this, "RootPane.ancestorInputMap");
        }
        if (condition == JComponent.WHEN_IN_FOCUSED_WINDOW) {
            return createInputMap(condition, c);
        }
        return null;
    }
    
    ComponentInputMap createInputMap(int condition, JComponent c) {
        return new BasicRootPaneUI$RootPaneInputMap(c);
    }
    
    static void loadActionMap(LazyActionMap map) {
        map.put(new BasicRootPaneUI$Actions(BasicRootPaneUI$Actions.PRESS));
        map.put(new BasicRootPaneUI$Actions(BasicRootPaneUI$Actions.RELEASE));
        map.put(new BasicRootPaneUI$Actions(BasicRootPaneUI$Actions.POST_POPUP));
    }
    
    void updateDefaultButtonBindings(JRootPane root) {
        InputMap km = SwingUtilities.getUIInputMap(root, JComponent.WHEN_IN_FOCUSED_WINDOW);
        while (km != null && !(km instanceof BasicRootPaneUI$RootPaneInputMap)) {
            km = km.getParent();
        }
        if (km != null) {
            km.clear();
            if (root.getDefaultButton() != null) {
                Object[] bindings = (Object[])(Object[])DefaultLookup.get(root, this, "RootPane.defaultButtonWindowKeyBindings");
                if (bindings != null) {
                    LookAndFeel.loadKeyBindings(km, bindings);
                }
            }
        }
    }
    
    public void propertyChange(PropertyChangeEvent e) {
        if (e.getPropertyName().equals("defaultButton")) {
            JRootPane rootpane = (JRootPane)(JRootPane)e.getSource();
            updateDefaultButtonBindings(rootpane);
            if (rootpane.getClientProperty("temporaryDefaultButton") == null) {
                rootpane.putClientProperty("initialDefaultButton", e.getNewValue());
            }
        }
    }
    {
    }
    {
    }
}
