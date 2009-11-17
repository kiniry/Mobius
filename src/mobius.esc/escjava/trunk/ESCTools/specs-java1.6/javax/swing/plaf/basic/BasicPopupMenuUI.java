package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.plaf.basic.*;
import javax.swing.border.*;
import java.awt.Component;
import java.awt.event.*;
import java.util.*;

public class BasicPopupMenuUI extends PopupMenuUI {
    
    /*synthetic*/ static boolean access$500(MenuElement x0, MenuElement x1) {
        return checkInvokerEqual(x0, x1);
    }
    
    /*synthetic*/ static boolean access$300() {
        return doUnpostPopupOnDeactivation();
    }
    protected JPopupMenu popupMenu = null;
    private transient PopupMenuListener popupMenuListener = null;
    private MenuKeyListener menuKeyListener = null;
    static boolean menuKeyboardHelperInstalled = false;
    static BasicPopupMenuUI$MenuKeyboardHelper menuKeyboardHelper = null;
    private static boolean checkedUnpostPopup;
    private static boolean unpostPopup;
    
    public static ComponentUI createUI(JComponent x) {
        return new BasicPopupMenuUI();
    }
    
    public BasicPopupMenuUI() {
        
        BasicLookAndFeel.hasPopups = true;
        LookAndFeel laf = UIManager.getLookAndFeel();
        if (laf instanceof BasicLookAndFeel) {
            ((BasicLookAndFeel)(BasicLookAndFeel)laf).createdPopup();
        }
    }
    
    public void installUI(JComponent c) {
        popupMenu = (JPopupMenu)(JPopupMenu)c;
        installDefaults();
        installListeners();
        installKeyboardActions();
    }
    
    public void installDefaults() {
        if (popupMenu.getLayout() == null || popupMenu.getLayout() instanceof UIResource) popupMenu.setLayout(new DefaultMenuLayout(popupMenu, BoxLayout.Y_AXIS));
        LookAndFeel.installProperty(popupMenu, "opaque", Boolean.TRUE);
        LookAndFeel.installBorder(popupMenu, "PopupMenu.border");
        LookAndFeel.installColorsAndFont(popupMenu, "PopupMenu.background", "PopupMenu.foreground", "PopupMenu.font");
    }
    
    protected void installListeners() {
        if (popupMenuListener == null) {
            popupMenuListener = new BasicPopupMenuUI$BasicPopupMenuListener(this, null);
        }
        popupMenu.addPopupMenuListener(popupMenuListener);
        if (menuKeyListener == null) {
            menuKeyListener = new BasicPopupMenuUI$BasicMenuKeyListener(this, null);
        }
        popupMenu.addMenuKeyListener(menuKeyListener);
        if (mouseGrabber == null) {
            mouseGrabber = new BasicPopupMenuUI$MouseGrabber();
        }
        if (!menuKeyboardHelperInstalled) {
            if (menuKeyboardHelper == null) {
                menuKeyboardHelper = new BasicPopupMenuUI$MenuKeyboardHelper(null);
            }
            MenuSelectionManager msm = MenuSelectionManager.defaultManager();
            msm.addChangeListener(menuKeyboardHelper);
            menuKeyboardHelperInstalled = true;
        }
    }
    
    protected void installKeyboardActions() {
    }
    
    static InputMap getInputMap(JPopupMenu popup, JComponent c) {
        InputMap windowInputMap = null;
        Object[] bindings = (Object[])(Object[])UIManager.get("PopupMenu.selectedWindowInputMapBindings");
        if (bindings != null) {
            windowInputMap = LookAndFeel.makeComponentInputMap(c, bindings);
            if (!popup.getComponentOrientation().isLeftToRight()) {
                Object[] km = (Object[])(Object[])UIManager.get("PopupMenu.selectedWindowInputMapBindings.RightToLeft");
                if (km != null) {
                    InputMap rightToLeftInputMap = LookAndFeel.makeComponentInputMap(c, km);
                    rightToLeftInputMap.setParent(windowInputMap);
                    windowInputMap = rightToLeftInputMap;
                }
            }
        }
        return windowInputMap;
    }
    
    static ActionMap getActionMap() {
        return LazyActionMap.getActionMap(BasicPopupMenuUI.class, "PopupMenu.actionMap");
    }
    
    static void loadActionMap(LazyActionMap map) {
        map.put(new BasicPopupMenuUI$Actions("cancel"));
        map.put(new BasicPopupMenuUI$Actions("selectNext"));
        map.put(new BasicPopupMenuUI$Actions("selectPrevious"));
        map.put(new BasicPopupMenuUI$Actions("selectParent"));
        map.put(new BasicPopupMenuUI$Actions("selectChild"));
        map.put(new BasicPopupMenuUI$Actions("return"));
        BasicLookAndFeel.installAudioActionMap(map);
    }
    
    public void uninstallUI(JComponent c) {
        uninstallDefaults();
        uninstallListeners();
        uninstallKeyboardActions();
        popupMenu = null;
    }
    
    protected void uninstallDefaults() {
        LookAndFeel.uninstallBorder(popupMenu);
    }
    
    protected void uninstallListeners() {
        if (popupMenuListener != null) {
            popupMenu.removePopupMenuListener(popupMenuListener);
        }
        if (menuKeyListener != null) {
            popupMenu.removeMenuKeyListener(menuKeyListener);
        }
        if (mouseGrabber != null) {
            MenuSelectionManager msm = MenuSelectionManager.defaultManager();
            msm.removeChangeListener(mouseGrabber);
            mouseGrabber.ungrabWindow();
            mouseGrabber = null;
        }
    }
    
    protected void uninstallKeyboardActions() {
        SwingUtilities.replaceUIActionMap(popupMenu, null);
        SwingUtilities.replaceUIInputMap(popupMenu, JComponent.WHEN_IN_FOCUSED_WINDOW, null);
    }
    
    static MenuElement getFirstPopup() {
        MenuSelectionManager msm = MenuSelectionManager.defaultManager();
        MenuElement[] p = msm.getSelectedPath();
        MenuElement me = null;
        for (int i = 0; me == null && i < p.length; i++) {
            if (p[i] instanceof JPopupMenu) me = p[i];
        }
        return me;
    }
    
    private static boolean doUnpostPopupOnDeactivation() {
        if (!checkedUnpostPopup) {
            Boolean b = (Boolean)java.security.AccessController.doPrivileged(new BasicPopupMenuUI$1());
            unpostPopup = b.booleanValue();
            checkedUnpostPopup = true;
        }
        return unpostPopup;
    }
    
    static JPopupMenu getLastPopup() {
        MenuSelectionManager msm = MenuSelectionManager.defaultManager();
        MenuElement[] p = msm.getSelectedPath();
        JPopupMenu popup = null;
        for (int i = p.length - 1; popup == null && i >= 0; i--) {
            if (p[i] instanceof JPopupMenu) popup = (JPopupMenu)(JPopupMenu)p[i];
        }
        return popup;
    }
    
    static List getPopups() {
        MenuSelectionManager msm = MenuSelectionManager.defaultManager();
        MenuElement[] p = msm.getSelectedPath();
        List list = new ArrayList(p.length);
        for (int i = 0; i < p.length; i++) {
            if (p[i] instanceof JPopupMenu) {
                list.add((JPopupMenu)(JPopupMenu)p[i]);
            }
        }
        return list;
    }
    
    public boolean isPopupTrigger(MouseEvent e) {
        return ((e.getID() == MouseEvent.MOUSE_RELEASED) && ((e.getModifiers() & MouseEvent.BUTTON3_MASK) != 0));
    }
    
    private static boolean checkInvokerEqual(MenuElement present, MenuElement last) {
        Component invokerPresent = present.getComponent();
        Component invokerLast = last.getComponent();
        if (invokerPresent instanceof JPopupMenu) {
            invokerPresent = ((JPopupMenu)(JPopupMenu)invokerPresent).getInvoker();
        }
        if (invokerLast instanceof JPopupMenu) {
            invokerLast = ((JPopupMenu)(JPopupMenu)invokerLast).getInvoker();
        }
        return (invokerPresent == invokerLast);
    }
    {
    }
    {
    }
    {
    }
    
    private static MenuElement nextEnabledChild(MenuElement[] e, int fromIndex, int toIndex) {
        for (int i = fromIndex; i <= toIndex; i++) {
            if (e[i] != null) {
                Component comp = e[i].getComponent();
                if (comp != null && comp.isEnabled() && comp.isVisible()) {
                    return e[i];
                }
            }
        }
        return null;
    }
    
    private static MenuElement previousEnabledChild(MenuElement[] e, int fromIndex, int toIndex) {
        for (int i = fromIndex; i >= toIndex; i--) {
            if (e[i] != null) {
                Component comp = e[i].getComponent();
                if (comp != null && comp.isEnabled() && comp.isVisible()) {
                    return e[i];
                }
            }
        }
        return null;
    }
    
    static MenuElement findEnabledChild(MenuElement[] e, int fromIndex, boolean forward) {
        MenuElement result = null;
        if (forward) {
            result = nextEnabledChild(e, fromIndex + 1, e.length - 1);
            if (result == null) result = nextEnabledChild(e, 0, fromIndex - 1);
        } else {
            result = previousEnabledChild(e, fromIndex - 1, 0);
            if (result == null) result = previousEnabledChild(e, e.length - 1, fromIndex + 1);
        }
        return result;
    }
    
    static MenuElement findEnabledChild(MenuElement[] e, MenuElement elem, boolean forward) {
        for (int i = 0; i < e.length; i++) {
            if (e[i] == elem) {
                return findEnabledChild(e, i, forward);
            }
        }
        return null;
    }
    private static transient BasicPopupMenuUI$MouseGrabber mouseGrabber = null;
    {
    }
    {
    }
}
