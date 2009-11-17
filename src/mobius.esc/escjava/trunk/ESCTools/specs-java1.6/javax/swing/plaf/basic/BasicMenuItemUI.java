package javax.swing.plaf.basic;

import sun.swing.MenuItemCheckIconFactory;
import com.sun.java.swing.SwingUtilities2;
import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.border.*;
import javax.swing.plaf.*;
import javax.swing.text.View;

public class BasicMenuItemUI extends MenuItemUI {
    
    public BasicMenuItemUI() {
        
    }
    protected JMenuItem menuItem = null;
    protected Color selectionBackground;
    protected Color selectionForeground;
    protected Color disabledForeground;
    protected Color acceleratorForeground;
    protected Color acceleratorSelectionForeground;
    private String acceleratorDelimiter;
    protected int defaultTextIconGap;
    protected Font acceleratorFont;
    protected MouseInputListener mouseInputListener;
    protected MenuDragMouseListener menuDragMouseListener;
    protected MenuKeyListener menuKeyListener;
    BasicMenuItemUI$Handler handler;
    protected Icon arrowIcon = null;
    protected Icon checkIcon = null;
    protected boolean oldBorderPainted;
    private static final boolean TRACE = false;
    private static final boolean VERBOSE = false;
    private static final boolean DEBUG = false;
    static final String MAX_TEXT_WIDTH = "maxTextWidth";
    static final String MAX_ACC_WIDTH = "maxAccWidth";
    
    static void loadActionMap(LazyActionMap map) {
        map.put(new BasicMenuItemUI$Actions("doClick"));
        BasicLookAndFeel.installAudioActionMap(map);
    }
    
    public static ComponentUI createUI(JComponent c) {
        return new BasicMenuItemUI();
    }
    
    public void installUI(JComponent c) {
        menuItem = (JMenuItem)(JMenuItem)c;
        installDefaults();
        installComponents(menuItem);
        installListeners();
        installKeyboardActions();
    }
    
    protected void installDefaults() {
        String prefix = getPropertyPrefix();
        acceleratorFont = UIManager.getFont("MenuItem.acceleratorFont");
        Object opaque = UIManager.get(getPropertyPrefix() + ".opaque");
        if (opaque != null) {
            LookAndFeel.installProperty(menuItem, "opaque", opaque);
        } else {
            LookAndFeel.installProperty(menuItem, "opaque", Boolean.TRUE);
        }
        if (menuItem.getMargin() == null || (menuItem.getMargin() instanceof UIResource)) {
            menuItem.setMargin(UIManager.getInsets(prefix + ".margin"));
        }
        defaultTextIconGap = 4;
        LookAndFeel.installBorder(menuItem, prefix + ".border");
        oldBorderPainted = menuItem.isBorderPainted();
        LookAndFeel.installProperty(menuItem, "borderPainted", UIManager.get(prefix + ".borderPainted"));
        LookAndFeel.installColorsAndFont(menuItem, prefix + ".background", prefix + ".foreground", prefix + ".font");
        if (selectionBackground == null || selectionBackground instanceof UIResource) {
            selectionBackground = UIManager.getColor(prefix + ".selectionBackground");
        }
        if (selectionForeground == null || selectionForeground instanceof UIResource) {
            selectionForeground = UIManager.getColor(prefix + ".selectionForeground");
        }
        if (disabledForeground == null || disabledForeground instanceof UIResource) {
            disabledForeground = UIManager.getColor(prefix + ".disabledForeground");
        }
        if (acceleratorForeground == null || acceleratorForeground instanceof UIResource) {
            acceleratorForeground = UIManager.getColor(prefix + ".acceleratorForeground");
        }
        if (acceleratorSelectionForeground == null || acceleratorSelectionForeground instanceof UIResource) {
            acceleratorSelectionForeground = UIManager.getColor(prefix + ".acceleratorSelectionForeground");
        }
        acceleratorDelimiter = UIManager.getString("MenuItem.acceleratorDelimiter");
        if (acceleratorDelimiter == null) {
            acceleratorDelimiter = "+";
        }
        if (arrowIcon == null || arrowIcon instanceof UIResource) {
            arrowIcon = UIManager.getIcon(prefix + ".arrowIcon");
        }
        if (checkIcon == null || checkIcon instanceof UIResource) {
            checkIcon = UIManager.getIcon(prefix + ".checkIcon");
            MenuItemCheckIconFactory iconFactory = (MenuItemCheckIconFactory)(MenuItemCheckIconFactory)UIManager.get(prefix + ".checkIconFactory");
            if (iconFactory != null && iconFactory.isCompatible(checkIcon, prefix)) {
                checkIcon = iconFactory.getIcon(menuItem);
            }
        }
    }
    
    protected void installComponents(JMenuItem menuItem) {
        BasicHTML.updateRenderer(menuItem, menuItem.getText());
    }
    
    protected String getPropertyPrefix() {
        return "MenuItem";
    }
    
    protected void installListeners() {
        if ((mouseInputListener = createMouseInputListener(menuItem)) != null) {
            menuItem.addMouseListener(mouseInputListener);
            menuItem.addMouseMotionListener(mouseInputListener);
        }
        if ((menuDragMouseListener = createMenuDragMouseListener(menuItem)) != null) {
            menuItem.addMenuDragMouseListener(menuDragMouseListener);
        }
        if ((menuKeyListener = createMenuKeyListener(menuItem)) != null) {
            menuItem.addMenuKeyListener(menuKeyListener);
        }
        menuItem.addPropertyChangeListener(getHandler());
    }
    
    protected void installKeyboardActions() {
        installLazyActionMap();
        updateAcceleratorBinding();
    }
    
    void installLazyActionMap() {
        LazyActionMap.installLazyActionMap(menuItem, BasicMenuItemUI.class, getPropertyPrefix() + ".actionMap");
    }
    
    public void uninstallUI(JComponent c) {
        menuItem = (JMenuItem)(JMenuItem)c;
        uninstallDefaults();
        uninstallComponents(menuItem);
        uninstallListeners();
        uninstallKeyboardActions();
        Container parent = menuItem.getParent();
        if ((parent != null && parent instanceof JComponent) && !(menuItem instanceof JMenu && ((JMenu)(JMenu)menuItem).isTopLevelMenu())) {
            JComponent p = (JComponent)(JComponent)parent;
            p.putClientProperty(BasicMenuItemUI.MAX_ACC_WIDTH, null);
            p.putClientProperty(BasicMenuItemUI.MAX_TEXT_WIDTH, null);
        }
        menuItem = null;
    }
    
    protected void uninstallDefaults() {
        LookAndFeel.uninstallBorder(menuItem);
        if (menuItem.getMargin() instanceof UIResource) menuItem.setMargin(null);
        if (arrowIcon instanceof UIResource) arrowIcon = null;
        if (checkIcon instanceof UIResource) checkIcon = null;
    }
    
    protected void uninstallComponents(JMenuItem menuItem) {
        BasicHTML.updateRenderer(menuItem, "");
    }
    
    protected void uninstallListeners() {
        if (mouseInputListener != null) {
            menuItem.removeMouseListener(mouseInputListener);
            menuItem.removeMouseMotionListener(mouseInputListener);
        }
        if (menuDragMouseListener != null) {
            menuItem.removeMenuDragMouseListener(menuDragMouseListener);
        }
        if (menuKeyListener != null) {
            menuItem.removeMenuKeyListener(menuKeyListener);
        }
        menuItem.removePropertyChangeListener(getHandler());
        mouseInputListener = null;
        menuDragMouseListener = null;
        menuKeyListener = null;
        handler = null;
    }
    
    protected void uninstallKeyboardActions() {
        SwingUtilities.replaceUIActionMap(menuItem, null);
        SwingUtilities.replaceUIInputMap(menuItem, JComponent.WHEN_IN_FOCUSED_WINDOW, null);
    }
    
    protected MouseInputListener createMouseInputListener(JComponent c) {
        return getHandler();
    }
    
    protected MenuDragMouseListener createMenuDragMouseListener(JComponent c) {
        return getHandler();
    }
    
    protected MenuKeyListener createMenuKeyListener(JComponent c) {
        return null;
    }
    
    BasicMenuItemUI$Handler getHandler() {
        if (handler == null) {
            handler = new BasicMenuItemUI$Handler(this);
        }
        return handler;
    }
    
    InputMap createInputMap(int condition) {
        if (condition == JComponent.WHEN_IN_FOCUSED_WINDOW) {
            return new ComponentInputMapUIResource(menuItem);
        }
        return null;
    }
    
    void updateAcceleratorBinding() {
        KeyStroke accelerator = menuItem.getAccelerator();
        InputMap windowInputMap = SwingUtilities.getUIInputMap(menuItem, JComponent.WHEN_IN_FOCUSED_WINDOW);
        if (windowInputMap != null) {
            windowInputMap.clear();
        }
        if (accelerator != null) {
            if (windowInputMap == null) {
                windowInputMap = createInputMap(JComponent.WHEN_IN_FOCUSED_WINDOW);
                SwingUtilities.replaceUIInputMap(menuItem, JComponent.WHEN_IN_FOCUSED_WINDOW, windowInputMap);
            }
            windowInputMap.put(accelerator, "doClick");
        }
    }
    
    public Dimension getMinimumSize(JComponent c) {
        Dimension d = null;
        View v = (View)(View)c.getClientProperty(BasicHTML.propertyKey);
        if (v != null) {
            d = getPreferredSize(c);
            d.width -= v.getPreferredSpan(View.X_AXIS) - v.getMinimumSpan(View.X_AXIS);
        }
        return d;
    }
    
    public Dimension getPreferredSize(JComponent c) {
        return getPreferredMenuItemSize(c, checkIcon, arrowIcon, defaultTextIconGap);
    }
    
    public Dimension getMaximumSize(JComponent c) {
        Dimension d = null;
        View v = (View)(View)c.getClientProperty(BasicHTML.propertyKey);
        if (v != null) {
            d = getPreferredSize(c);
            d.width += v.getMaximumSpan(View.X_AXIS) - v.getPreferredSpan(View.X_AXIS);
        }
        return d;
    }
    static Rectangle zeroRect = new Rectangle(0, 0, 0, 0);
    static Rectangle iconRect = new Rectangle();
    static Rectangle textRect = new Rectangle();
    static Rectangle acceleratorRect = new Rectangle();
    static Rectangle checkIconRect = new Rectangle();
    static Rectangle arrowIconRect = new Rectangle();
    static Rectangle viewRect = new Rectangle(Short.MAX_VALUE, Short.MAX_VALUE);
    static Rectangle r = new Rectangle();
    
    private void resetRects() {
        iconRect.setBounds(zeroRect);
        textRect.setBounds(zeroRect);
        acceleratorRect.setBounds(zeroRect);
        checkIconRect.setBounds(zeroRect);
        arrowIconRect.setBounds(zeroRect);
        viewRect.setBounds(0, 0, Short.MAX_VALUE, Short.MAX_VALUE);
        r.setBounds(zeroRect);
    }
    
    protected Dimension getPreferredMenuItemSize(JComponent c, Icon checkIcon, Icon arrowIcon, int defaultTextIconGap) {
        JMenuItem b = (JMenuItem)(JMenuItem)c;
        Icon icon = null;
        MenuItemCheckIconFactory iconFactory = (MenuItemCheckIconFactory)(MenuItemCheckIconFactory)UIManager.get(getPropertyPrefix() + ".checkIconFactory");
        if (iconFactory == null || !iconFactory.isCompatible(checkIcon, getPropertyPrefix())) {
            icon = b.getIcon();
        }
        String text = b.getText();
        KeyStroke accelerator = b.getAccelerator();
        String acceleratorText = "";
        if (accelerator != null) {
            int modifiers = accelerator.getModifiers();
            if (modifiers > 0) {
                acceleratorText = KeyEvent.getKeyModifiersText(modifiers);
                acceleratorText += acceleratorDelimiter;
            }
            int keyCode = accelerator.getKeyCode();
            if (keyCode != 0) {
                acceleratorText += KeyEvent.getKeyText(keyCode);
            } else {
                acceleratorText += accelerator.getKeyChar();
            }
        }
        Font font = b.getFont();
        FontMetrics fm = b.getFontMetrics(font);
        FontMetrics fmAccel = b.getFontMetrics(acceleratorFont);
        resetRects();
        layoutMenuItem(fm, text, fmAccel, acceleratorText, icon, checkIcon, arrowIcon, b.getVerticalAlignment(), b.getHorizontalAlignment(), b.getVerticalTextPosition(), b.getHorizontalTextPosition(), viewRect, iconRect, textRect, acceleratorRect, checkIconRect, arrowIconRect, text == null ? 0 : defaultTextIconGap, defaultTextIconGap);
        r.setBounds(textRect);
        r = SwingUtilities.computeUnion(iconRect.x, iconRect.y, iconRect.width, iconRect.height, r);
        r.height = Math.max(Math.max(r.height, checkIconRect.height), Math.max(arrowIconRect.height, acceleratorRect.height));
        Container parent = menuItem.getParent();
        if (parent != null && parent instanceof JComponent && !(menuItem instanceof JMenu && ((JMenu)(JMenu)menuItem).isTopLevelMenu())) {
            JComponent p = (JComponent)(JComponent)parent;
            Integer maxTextWidth = (Integer)(Integer)p.getClientProperty(BasicMenuItemUI.MAX_TEXT_WIDTH);
            Integer maxAccWidth = (Integer)(Integer)p.getClientProperty(BasicMenuItemUI.MAX_ACC_WIDTH);
            int maxTextValue = maxTextWidth != null ? maxTextWidth.intValue() : 0;
            int maxAccValue = maxAccWidth != null ? maxAccWidth.intValue() : 0;
            if (r.width < maxTextValue) {
                r.width = maxTextValue;
            } else {
                p.putClientProperty(BasicMenuItemUI.MAX_TEXT_WIDTH, new Integer(r.width));
            }
            if (acceleratorRect.width > maxAccValue) {
                maxAccValue = acceleratorRect.width;
                p.putClientProperty(BasicMenuItemUI.MAX_ACC_WIDTH, new Integer(acceleratorRect.width));
            }
            r.width += maxAccValue;
            r.width += defaultTextIconGap;
        }
        if (useCheckAndArrow()) {
            r.width += checkIconRect.width;
            r.width += defaultTextIconGap;
            r.width += defaultTextIconGap;
            r.width += arrowIconRect.width;
        }
        r.width += 2 * defaultTextIconGap;
        Insets insets = b.getInsets();
        if (insets != null) {
            r.width += insets.left + insets.right;
            r.height += insets.top + insets.bottom;
        }
        if (r.width % 2 == 0) {
            r.width++;
        }
        if (r.height % 2 == 0 && Boolean.TRUE != UIManager.get(getPropertyPrefix() + ".evenHeight")) {
            r.height++;
        }
        return r.getSize();
    }
    
    public void update(Graphics g, JComponent c) {
        paint(g, c);
    }
    
    public void paint(Graphics g, JComponent c) {
        paintMenuItem(g, c, checkIcon, arrowIcon, selectionBackground, selectionForeground, defaultTextIconGap);
    }
    
    protected void paintMenuItem(Graphics g, JComponent c, Icon checkIcon, Icon arrowIcon, Color background, Color foreground, int defaultTextIconGap) {
        JMenuItem b = (JMenuItem)(JMenuItem)c;
        ButtonModel model = b.getModel();
        int menuWidth = b.getWidth();
        int menuHeight = b.getHeight();
        Insets i = c.getInsets();
        resetRects();
        viewRect.setBounds(0, 0, menuWidth, menuHeight);
        viewRect.x += i.left;
        viewRect.y += i.top;
        viewRect.width -= (i.right + viewRect.x);
        viewRect.height -= (i.bottom + viewRect.y);
        Font holdf = g.getFont();
        Font f = c.getFont();
        g.setFont(f);
        FontMetrics fm = SwingUtilities2.getFontMetrics(c, g, f);
        FontMetrics fmAccel = SwingUtilities2.getFontMetrics(c, g, acceleratorFont);
        KeyStroke accelerator = b.getAccelerator();
        String acceleratorText = "";
        if (accelerator != null) {
            int modifiers = accelerator.getModifiers();
            if (modifiers > 0) {
                acceleratorText = KeyEvent.getKeyModifiersText(modifiers);
                acceleratorText += acceleratorDelimiter;
            }
            int keyCode = accelerator.getKeyCode();
            if (keyCode != 0) {
                acceleratorText += KeyEvent.getKeyText(keyCode);
            } else {
                acceleratorText += accelerator.getKeyChar();
            }
        }
        Icon icon = null;
        MenuItemCheckIconFactory iconFactory = (MenuItemCheckIconFactory)(MenuItemCheckIconFactory)UIManager.get(getPropertyPrefix() + ".checkIconFactory");
        if (iconFactory == null || !iconFactory.isCompatible(checkIcon, getPropertyPrefix())) {
            icon = b.getIcon();
        }
        String text = layoutMenuItem(fm, b.getText(), fmAccel, acceleratorText, icon, checkIcon, arrowIcon, b.getVerticalAlignment(), b.getHorizontalAlignment(), b.getVerticalTextPosition(), b.getHorizontalTextPosition(), viewRect, iconRect, textRect, acceleratorRect, checkIconRect, arrowIconRect, b.getText() == null ? 0 : defaultTextIconGap, defaultTextIconGap);
        paintBackground(g, b, background);
        Color holdc = g.getColor();
        if (checkIcon != null) {
            if (model.isArmed() || (c instanceof JMenu && model.isSelected())) {
                g.setColor(foreground);
            } else {
                g.setColor(holdc);
            }
            if (useCheckAndArrow()) checkIcon.paintIcon(c, g, checkIconRect.x, checkIconRect.y);
            g.setColor(holdc);
        }
        if (icon != null) {
            if (!model.isEnabled()) {
                icon = (Icon)b.getDisabledIcon();
            } else if (model.isPressed() && model.isArmed()) {
                icon = (Icon)b.getPressedIcon();
                if (icon == null) {
                    icon = (Icon)b.getIcon();
                }
            } else {
                icon = (Icon)b.getIcon();
            }
            if (icon != null) icon.paintIcon(c, g, iconRect.x, iconRect.y);
        }
        if (text != null) {
            View v = (View)(View)c.getClientProperty(BasicHTML.propertyKey);
            if (v != null) {
                v.paint(g, textRect);
            } else {
                paintText(g, b, textRect, text);
            }
        }
        if (acceleratorText != null && !acceleratorText.equals("")) {
            int accOffset = 0;
            Container parent = menuItem.getParent();
            if (parent != null && parent instanceof JComponent) {
                JComponent p = (JComponent)(JComponent)parent;
                Integer maxValueInt = (Integer)(Integer)p.getClientProperty(BasicMenuItemUI.MAX_ACC_WIDTH);
                int maxValue = maxValueInt != null ? maxValueInt.intValue() : acceleratorRect.width;
                accOffset = maxValue - acceleratorRect.width;
            }
            g.setFont(acceleratorFont);
            if (!model.isEnabled()) {
                if (disabledForeground != null) {
                    g.setColor(disabledForeground);
                    SwingUtilities2.drawString(b, g, acceleratorText, acceleratorRect.x - accOffset, acceleratorRect.y + fmAccel.getAscent());
                } else {
                    g.setColor(b.getBackground().brighter());
                    SwingUtilities2.drawString(b, g, acceleratorText, acceleratorRect.x - accOffset, acceleratorRect.y + fmAccel.getAscent());
                    g.setColor(b.getBackground().darker());
                    SwingUtilities2.drawString(b, g, acceleratorText, acceleratorRect.x - accOffset - 1, acceleratorRect.y + fmAccel.getAscent() - 1);
                }
            } else {
                if (model.isArmed() || (c instanceof JMenu && model.isSelected())) {
                    g.setColor(acceleratorSelectionForeground);
                } else {
                    g.setColor(acceleratorForeground);
                }
                SwingUtilities2.drawString(b, g, acceleratorText, acceleratorRect.x - accOffset, acceleratorRect.y + fmAccel.getAscent());
            }
        }
        if (arrowIcon != null) {
            if (model.isArmed() || (c instanceof JMenu && model.isSelected())) g.setColor(foreground);
            if (useCheckAndArrow()) arrowIcon.paintIcon(c, g, arrowIconRect.x, arrowIconRect.y);
        }
        g.setColor(holdc);
        g.setFont(holdf);
    }
    
    protected void paintBackground(Graphics g, JMenuItem menuItem, Color bgColor) {
        ButtonModel model = menuItem.getModel();
        Color oldColor = g.getColor();
        int menuWidth = menuItem.getWidth();
        int menuHeight = menuItem.getHeight();
        if (menuItem.isOpaque()) {
            if (model.isArmed() || (menuItem instanceof JMenu && model.isSelected())) {
                g.setColor(bgColor);
                g.fillRect(0, 0, menuWidth, menuHeight);
            } else {
                g.setColor(menuItem.getBackground());
                g.fillRect(0, 0, menuWidth, menuHeight);
            }
            g.setColor(oldColor);
        } else if (model.isArmed() || (menuItem instanceof JMenu && model.isSelected())) {
            g.setColor(bgColor);
            g.fillRect(0, 0, menuWidth, menuHeight);
            g.setColor(oldColor);
        }
    }
    
    protected void paintText(Graphics g, JMenuItem menuItem, Rectangle textRect, String text) {
        ButtonModel model = menuItem.getModel();
        FontMetrics fm = SwingUtilities2.getFontMetrics(menuItem, g);
        int mnemIndex = menuItem.getDisplayedMnemonicIndex();
        if (!model.isEnabled()) {
            if (UIManager.get("MenuItem.disabledForeground") instanceof Color) {
                g.setColor(UIManager.getColor("MenuItem.disabledForeground"));
                SwingUtilities2.drawStringUnderlineCharAt(menuItem, g, text, mnemIndex, textRect.x, textRect.y + fm.getAscent());
            } else {
                g.setColor(menuItem.getBackground().brighter());
                SwingUtilities2.drawStringUnderlineCharAt(menuItem, g, text, mnemIndex, textRect.x, textRect.y + fm.getAscent());
                g.setColor(menuItem.getBackground().darker());
                SwingUtilities2.drawStringUnderlineCharAt(menuItem, g, text, mnemIndex, textRect.x - 1, textRect.y + fm.getAscent() - 1);
            }
        } else {
            if (model.isArmed() || (menuItem instanceof JMenu && model.isSelected())) {
                g.setColor(selectionForeground);
            }
            SwingUtilities2.drawStringUnderlineCharAt(menuItem, g, text, mnemIndex, textRect.x, textRect.y + fm.getAscent());
        }
    }
    
    private String layoutMenuItem(FontMetrics fm, String text, FontMetrics fmAccel, String acceleratorText, Icon icon, Icon checkIcon, Icon arrowIcon, int verticalAlignment, int horizontalAlignment, int verticalTextPosition, int horizontalTextPosition, Rectangle viewRect, Rectangle iconRect, Rectangle textRect, Rectangle acceleratorRect, Rectangle checkIconRect, Rectangle arrowIconRect, int textIconGap, int menuItemGap) {
        SwingUtilities.layoutCompoundLabel(menuItem, fm, text, icon, verticalAlignment, horizontalAlignment, verticalTextPosition, horizontalTextPosition, viewRect, iconRect, textRect, textIconGap);
        if ((acceleratorText == null) || acceleratorText.equals("")) {
            acceleratorRect.width = acceleratorRect.height = 0;
            acceleratorText = "";
        } else {
            acceleratorRect.width = SwingUtilities2.stringWidth(menuItem, fmAccel, acceleratorText);
            acceleratorRect.height = fmAccel.getHeight();
        }
        if (useCheckAndArrow()) {
            if (checkIcon != null) {
                checkIconRect.width = checkIcon.getIconWidth();
                checkIconRect.height = checkIcon.getIconHeight();
            } else {
                checkIconRect.width = checkIconRect.height = 0;
            }
            if (arrowIcon != null) {
                arrowIconRect.width = arrowIcon.getIconWidth();
                arrowIconRect.height = arrowIcon.getIconHeight();
            } else {
                arrowIconRect.width = arrowIconRect.height = 0;
            }
        }
        Rectangle labelRect = iconRect.union(textRect);
        int checkIconOffset = menuItemGap;
        Object checkIconOffsetObject = UIManager.get(getPropertyPrefix() + ".checkIconOffset");
        if (checkIconOffsetObject instanceof Integer) {
            checkIconOffset = ((Integer)(Integer)checkIconOffsetObject).intValue();
        }
        if (BasicGraphicsUtils.isLeftToRight(menuItem)) {
            int minimumTextOffset = 0;
            Object minimumTextOffsetObject = UIManager.get(getPropertyPrefix() + ".minimumTextOffset");
            if (minimumTextOffsetObject instanceof Integer) {
                minimumTextOffset = ((Integer)(Integer)minimumTextOffsetObject).intValue();
            }
            textRect.x += menuItemGap;
            iconRect.x += menuItemGap;
            acceleratorRect.x = viewRect.x + viewRect.width - arrowIconRect.width - menuItemGap - acceleratorRect.width;
            if (useCheckAndArrow()) {
                checkIconRect.x = viewRect.x + checkIconOffset;
                textRect.x += checkIconOffset + checkIconRect.width;
                textRect.x = Math.max(textRect.x, minimumTextOffset);
                iconRect.x += checkIconOffset + checkIconRect.width;
                arrowIconRect.x = viewRect.x + viewRect.width - menuItemGap - arrowIconRect.width;
            }
        } else {
            textRect.x -= menuItemGap;
            iconRect.x -= menuItemGap;
            acceleratorRect.x = viewRect.x + arrowIconRect.width + menuItemGap;
            if (useCheckAndArrow()) {
                checkIconRect.x = viewRect.x + viewRect.width - menuItemGap - checkIconRect.width;
                textRect.x -= menuItemGap + checkIconRect.width;
                iconRect.x -= menuItemGap + checkIconRect.width;
                arrowIconRect.x = viewRect.x + menuItemGap;
            }
        }
        acceleratorRect.y = labelRect.y + (labelRect.height / 2) - (acceleratorRect.height / 2);
        if (useCheckAndArrow()) {
            arrowIconRect.y = labelRect.y + (labelRect.height / 2) - (arrowIconRect.height / 2);
            checkIconRect.y = labelRect.y + (labelRect.height / 2) - (checkIconRect.height / 2);
        }
        return text;
    }
    
    private boolean useCheckAndArrow() {
        boolean b = true;
        if ((menuItem instanceof JMenu) && (((JMenu)(JMenu)menuItem).isTopLevelMenu())) {
            b = false;
        }
        return b;
    }
    
    public MenuElement[] getPath() {
        MenuSelectionManager m = MenuSelectionManager.defaultManager();
        MenuElement[] oldPath = m.getSelectedPath();
        MenuElement[] newPath;
        int i = oldPath.length;
        if (i == 0) return new MenuElement[0];
        Component parent = menuItem.getParent();
        if (oldPath[i - 1].getComponent() == parent) {
            newPath = new MenuElement[i + 1];
            System.arraycopy(oldPath, 0, newPath, 0, i);
            newPath[i] = menuItem;
        } else {
            int j;
            for (j = oldPath.length - 1; j >= 0; j--) {
                if (oldPath[j].getComponent() == parent) break;
            }
            newPath = new MenuElement[j + 2];
            System.arraycopy(oldPath, 0, newPath, 0, j + 1);
            newPath[j + 1] = menuItem;
        }
        return newPath;
    }
    
    void printMenuElementArray(MenuElement[] path, boolean dumpStack) {
        System.out.println("Path is(");
        int i;
        int j;
        for (i = 0, j = path.length; i < j; i++) {
            for (int k = 0; k <= i; k++) System.out.print("  ");
            MenuElement me = (MenuElement)path[i];
            if (me instanceof JMenuItem) System.out.println(((JMenuItem)(JMenuItem)me).getText() + ", "); else if (me == null) System.out.println("NULL , "); else System.out.println("" + me + ", ");
        }
        System.out.println(")");
        if (dumpStack == true) Thread.dumpStack();
    }
    {
    }
    {
    }
    
    protected void doClick(MenuSelectionManager msm) {
        if (!isInternalFrameSystemMenu()) {
            BasicLookAndFeel.playSound(menuItem, getPropertyPrefix() + ".commandSound");
        }
        if (msm == null) {
            msm = MenuSelectionManager.defaultManager();
        }
        msm.clearSelectedPath();
        menuItem.doClick(0);
    }
    
    private boolean isInternalFrameSystemMenu() {
        String actionCommand = menuItem.getActionCommand();
        if ((actionCommand == "Close") || (actionCommand == "Minimize") || (actionCommand == "Restore") || (actionCommand == "Maximize")) {
            return true;
        } else {
            return false;
        }
    }
    {
    }
}
