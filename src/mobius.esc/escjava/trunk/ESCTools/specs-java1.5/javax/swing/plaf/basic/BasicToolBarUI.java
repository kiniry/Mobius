package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.util.Hashtable;
import java.util.HashMap;
import javax.swing.border.*;
import javax.swing.plaf.*;
import sun.swing.DefaultLookup;
import sun.swing.BorderProvider;

public class BasicToolBarUI extends ToolBarUI implements SwingConstants {
    
    /*synthetic*/ static BasicToolBarUI$Handler access$500(BasicToolBarUI x0) {
        return x0.getHandler();
    }
    
    /*synthetic*/ static Container access$402(BasicToolBarUI x0, Container x1) {
        return x0.dockingSource = x1;
    }
    
    /*synthetic*/ static Container access$400(BasicToolBarUI x0) {
        return x0.dockingSource;
    }
    
    /*synthetic*/ static RootPaneContainer access$302(BasicToolBarUI x0, RootPaneContainer x1) {
        return x0.floatingToolBar = x1;
    }
    
    /*synthetic*/ static RootPaneContainer access$300(BasicToolBarUI x0) {
        return x0.floatingToolBar;
    }
    
    /*synthetic*/ static boolean access$202(BasicToolBarUI x0, boolean x1) {
        return x0.floating = x1;
    }
    
    /*synthetic*/ static String access$100() {
        return IS_ROLLOVER;
    }
    
    public BasicToolBarUI() {
        
    }
    protected JToolBar toolBar;
    private boolean floating;
    private int floatingX;
    private int floatingY;
    private JFrame floatingFrame;
    private RootPaneContainer floatingToolBar;
    protected BasicToolBarUI$DragWindow dragWindow;
    private Container dockingSource;
    private int dockingSensitivity = 0;
    protected int focusedCompIndex = -1;
    protected Color dockingColor = null;
    protected Color floatingColor = null;
    protected Color dockingBorderColor = null;
    protected Color floatingBorderColor = null;
    protected MouseInputListener dockingListener;
    protected PropertyChangeListener propertyListener;
    protected ContainerListener toolBarContListener;
    protected FocusListener toolBarFocusListener;
    private BasicToolBarUI$Handler handler;
    protected String constraintBeforeFloating = BorderLayout.NORTH;
    private static String IS_ROLLOVER = "JToolBar.isRollover";
    private static Border rolloverBorder;
    private static Border nonRolloverBorder;
    private static Border nonRolloverToggleBorder;
    private boolean rolloverBorders = false;
    private HashMap borderTable = new HashMap();
    private Hashtable rolloverTable = new Hashtable();
    
    protected KeyStroke upKey;
    
    protected KeyStroke downKey;
    
    protected KeyStroke leftKey;
    
    protected KeyStroke rightKey;
    private static String FOCUSED_COMP_INDEX = "JToolBar.focusedCompIndex";
    
    public static ComponentUI createUI(JComponent c) {
        return new BasicToolBarUI();
    }
    
    public void installUI(JComponent c) {
        toolBar = (JToolBar)(JToolBar)c;
        installDefaults();
        installComponents();
        installListeners();
        installKeyboardActions();
        dockingSensitivity = 0;
        floating = false;
        floatingX = floatingY = 0;
        floatingToolBar = null;
        setOrientation(toolBar.getOrientation());
        LookAndFeel.installProperty(c, "opaque", Boolean.TRUE);
        if (c.getClientProperty(FOCUSED_COMP_INDEX) != null) {
            focusedCompIndex = ((Integer)((Integer)c.getClientProperty(FOCUSED_COMP_INDEX))).intValue();
        }
    }
    
    public void uninstallUI(JComponent c) {
        uninstallDefaults();
        uninstallComponents();
        uninstallListeners();
        uninstallKeyboardActions();
        if (isFloating() == true) setFloating(false, null);
        floatingToolBar = null;
        dragWindow = null;
        dockingSource = null;
        c.putClientProperty(FOCUSED_COMP_INDEX, new Integer(focusedCompIndex));
    }
    
    protected void installDefaults() {
        LookAndFeel.installBorder(toolBar, "ToolBar.border");
        LookAndFeel.installColorsAndFont(toolBar, "ToolBar.background", "ToolBar.foreground", "ToolBar.font");
        if (dockingColor == null || dockingColor instanceof UIResource) dockingColor = UIManager.getColor("ToolBar.dockingBackground");
        if (floatingColor == null || floatingColor instanceof UIResource) floatingColor = UIManager.getColor("ToolBar.floatingBackground");
        if (dockingBorderColor == null || dockingBorderColor instanceof UIResource) dockingBorderColor = UIManager.getColor("ToolBar.dockingForeground");
        if (floatingBorderColor == null || floatingBorderColor instanceof UIResource) floatingBorderColor = UIManager.getColor("ToolBar.floatingForeground");
        Object rolloverProp = toolBar.getClientProperty(IS_ROLLOVER);
        if (rolloverProp == null) {
            rolloverProp = UIManager.get("ToolBar.isRollover");
        }
        if (rolloverProp != null) {
            rolloverBorders = ((Boolean)(Boolean)rolloverProp).booleanValue();
        }
        if (rolloverBorder == null) {
            rolloverBorder = createRolloverBorder();
        }
        if (nonRolloverBorder == null) {
            nonRolloverBorder = createNonRolloverBorder();
        }
        if (nonRolloverToggleBorder == null) {
            nonRolloverToggleBorder = createNonRolloverToggleBorder();
        }
        setRolloverBorders(isRolloverBorders());
    }
    
    protected void uninstallDefaults() {
        LookAndFeel.uninstallBorder(toolBar);
        dockingColor = null;
        floatingColor = null;
        dockingBorderColor = null;
        floatingBorderColor = null;
        installNormalBorders(toolBar);
        rolloverBorder = null;
        nonRolloverBorder = null;
        nonRolloverToggleBorder = null;
    }
    
    protected void installComponents() {
    }
    
    protected void uninstallComponents() {
    }
    
    protected void installListeners() {
        dockingListener = createDockingListener();
        if (dockingListener != null) {
            toolBar.addMouseMotionListener(dockingListener);
            toolBar.addMouseListener(dockingListener);
        }
        propertyListener = createPropertyListener();
        if (propertyListener != null) {
            toolBar.addPropertyChangeListener(propertyListener);
        }
        toolBarContListener = createToolBarContListener();
        if (toolBarContListener != null) {
            toolBar.addContainerListener(toolBarContListener);
        }
        toolBarFocusListener = createToolBarFocusListener();
        if (toolBarFocusListener != null) {
            Component[] components = toolBar.getComponents();
            for (int i = 0; i < components.length; ++i) {
                components[i].addFocusListener(toolBarFocusListener);
            }
        }
    }
    
    protected void uninstallListeners() {
        if (dockingListener != null) {
            toolBar.removeMouseMotionListener(dockingListener);
            toolBar.removeMouseListener(dockingListener);
            dockingListener = null;
        }
        if (propertyListener != null) {
            toolBar.removePropertyChangeListener(propertyListener);
            propertyListener = null;
        }
        if (toolBarContListener != null) {
            toolBar.removeContainerListener(toolBarContListener);
            toolBarContListener = null;
        }
        if (toolBarFocusListener != null) {
            Component[] components = toolBar.getComponents();
            for (int i = 0; i < components.length; ++i) {
                components[i].removeFocusListener(toolBarFocusListener);
            }
            toolBarFocusListener = null;
        }
        handler = null;
    }
    
    protected void installKeyboardActions() {
        InputMap km = getInputMap(JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);
        SwingUtilities.replaceUIInputMap(toolBar, JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT, km);
        LazyActionMap.installLazyActionMap(toolBar, BasicToolBarUI.class, "ToolBar.actionMap");
    }
    
    InputMap getInputMap(int condition) {
        if (condition == JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT) {
            return (InputMap)(InputMap)DefaultLookup.get(toolBar, this, "ToolBar.ancestorInputMap");
        }
        return null;
    }
    
    static void loadActionMap(LazyActionMap map) {
        map.put(new BasicToolBarUI$Actions("navigateRight"));
        map.put(new BasicToolBarUI$Actions("navigateLeft"));
        map.put(new BasicToolBarUI$Actions("navigateUp"));
        map.put(new BasicToolBarUI$Actions("navigateDown"));
    }
    
    protected void uninstallKeyboardActions() {
        SwingUtilities.replaceUIActionMap(toolBar, null);
        SwingUtilities.replaceUIInputMap(toolBar, JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT, null);
    }
    
    protected void navigateFocusedComp(int direction) {
        int nComp = toolBar.getComponentCount();
        int j;
        switch (direction) {
        case EAST: 
        
        case SOUTH: 
            if (focusedCompIndex < 0 || focusedCompIndex >= nComp) break;
            j = focusedCompIndex + 1;
            while (j != focusedCompIndex) {
                if (j >= nComp) j = 0;
                Component comp = toolBar.getComponentAtIndex(j++);
                if (comp != null && comp.isFocusTraversable() && comp.isEnabled()) {
                    comp.requestFocus();
                    break;
                }
            }
            break;
        
        case WEST: 
        
        case NORTH: 
            if (focusedCompIndex < 0 || focusedCompIndex >= nComp) break;
            j = focusedCompIndex - 1;
            while (j != focusedCompIndex) {
                if (j < 0) j = nComp - 1;
                Component comp = toolBar.getComponentAtIndex(j--);
                if (comp != null && comp.isFocusTraversable() && comp.isEnabled()) {
                    comp.requestFocus();
                    break;
                }
            }
            break;
        
        default: 
            break;
        
        }
    }
    
    protected Border createRolloverBorder() {
        Object border = UIManager.get("ToolBar.rolloverBorder");
        if (border != null) {
            return (Border)(Border)border;
        }
        UIDefaults table = UIManager.getLookAndFeelDefaults();
        return new CompoundBorder(new BasicBorders$RolloverButtonBorder(table.getColor("controlShadow"), table.getColor("controlDkShadow"), table.getColor("controlHighlight"), table.getColor("controlLtHighlight")), new BasicBorders$RolloverMarginBorder());
    }
    
    protected Border createNonRolloverBorder() {
        Object border = UIManager.get("ToolBar.nonrolloverBorder");
        if (border != null) {
            return (Border)(Border)border;
        }
        UIDefaults table = UIManager.getLookAndFeelDefaults();
        return new CompoundBorder(new BasicBorders$ButtonBorder(table.getColor("Button.shadow"), table.getColor("Button.darkShadow"), table.getColor("Button.light"), table.getColor("Button.highlight")), new BasicBorders$RolloverMarginBorder());
    }
    
    private Border createNonRolloverToggleBorder() {
        UIDefaults table = UIManager.getLookAndFeelDefaults();
        return new CompoundBorder(new BasicBorders$RadioButtonBorder(table.getColor("ToggleButton.shadow"), table.getColor("ToggleButton.darkShadow"), table.getColor("ToggleButton.light"), table.getColor("ToggleButton.highlight")), new BasicBorders$RolloverMarginBorder());
    }
    
    protected JFrame createFloatingFrame(JToolBar toolbar) {
        Window window = SwingUtilities.getWindowAncestor(toolbar);
        JFrame frame = new BasicToolBarUI$1(this, toolbar.getName(), (window != null) ? window.getGraphicsConfiguration() : null);
        frame.getRootPane().setName("ToolBar.FloatingFrame");
        frame.setResizable(false);
        WindowListener wl = createFrameListener();
        frame.addWindowListener(wl);
        return frame;
    }
    
    protected RootPaneContainer createFloatingWindow(JToolBar toolbar) {
        {
        }
        JDialog dialog;
        Window window = SwingUtilities.getWindowAncestor(toolbar);
        if (window instanceof Frame) {
            dialog = new BasicToolBarUI$1ToolBarDialog(this, (Frame)(Frame)window, toolbar.getName(), false);
        } else if (window instanceof Dialog) {
            dialog = new BasicToolBarUI$1ToolBarDialog(this, (Dialog)(Dialog)window, toolbar.getName(), false);
        } else {
            dialog = new BasicToolBarUI$1ToolBarDialog(this, (Frame)null, toolbar.getName(), false);
        }
        dialog.getRootPane().setName("ToolBar.FloatingWindow");
        dialog.setTitle(toolbar.getName());
        dialog.setResizable(false);
        WindowListener wl = createFrameListener();
        dialog.addWindowListener(wl);
        return dialog;
    }
    
    protected BasicToolBarUI$DragWindow createDragWindow(JToolBar toolbar) {
        Window frame = null;
        if (toolBar != null) {
            Container p;
            for (p = toolBar.getParent(); p != null && !(p instanceof Window); p = p.getParent()) ;
            if (p != null && p instanceof Window) frame = (Window)(Window)p;
        }
        if (floatingToolBar == null) {
            floatingToolBar = createFloatingWindow(toolBar);
        }
        if (floatingToolBar instanceof Window) frame = (Window)(Window)floatingToolBar;
        BasicToolBarUI$DragWindow dragWindow = new BasicToolBarUI$DragWindow(this, frame);
        return dragWindow;
    }
    
    public boolean isRolloverBorders() {
        return rolloverBorders;
    }
    
    public void setRolloverBorders(boolean rollover) {
        rolloverBorders = rollover;
        if (rolloverBorders) {
            installRolloverBorders(toolBar);
        } else {
            installNonRolloverBorders(toolBar);
        }
    }
    
    protected void installRolloverBorders(JComponent c) {
        Component[] components = c.getComponents();
        for (int i = 0; i < components.length; ++i) {
            if (components[i] instanceof JComponent) {
                ((JComponent)(JComponent)components[i]).updateUI();
                setBorderToRollover(components[i]);
            }
        }
    }
    
    protected void installNonRolloverBorders(JComponent c) {
        Component[] components = c.getComponents();
        for (int i = 0; i < components.length; ++i) {
            if (components[i] instanceof JComponent) {
                ((JComponent)(JComponent)components[i]).updateUI();
                setBorderToNonRollover(components[i]);
            }
        }
    }
    
    protected void installNormalBorders(JComponent c) {
        Component[] components = c.getComponents();
        for (int i = 0; i < components.length; ++i) {
            setBorderToNormal(components[i]);
        }
    }
    
    protected void setBorderToRollover(Component c) {
        if (c instanceof AbstractButton) {
            AbstractButton b = (AbstractButton)(AbstractButton)c;
            Border border = (Border)(Border)borderTable.get(b);
            if (border == null || border instanceof UIResource) {
                borderTable.put(b, b.getBorder());
            }
            if (b.getBorder() instanceof UIResource) {
                b.setBorder(getRolloverBorder(b));
            }
            rolloverTable.put(b, b.isRolloverEnabled() ? Boolean.TRUE : Boolean.FALSE);
            b.setRolloverEnabled(true);
        }
    }
    
    private Border getRolloverBorder(AbstractButton b) {
        Object borderProvider = UIManager.get("ToolBar.rolloverBorderProvider");
        if (borderProvider == null) {
            return rolloverBorder;
        }
        return ((BorderProvider)(BorderProvider)borderProvider).getRolloverBorder(b);
    }
    
    protected void setBorderToNonRollover(Component c) {
        if (c instanceof AbstractButton) {
            AbstractButton b = (AbstractButton)(AbstractButton)c;
            Border border = (Border)(Border)borderTable.get(b);
            if (border == null || border instanceof UIResource) {
                borderTable.put(b, b.getBorder());
            }
            if (b.getBorder() instanceof UIResource) {
                if (b instanceof JToggleButton) {
                    ((JToggleButton)(JToggleButton)b).setBorder(nonRolloverToggleBorder);
                } else {
                    b.setBorder(nonRolloverBorder);
                }
            }
            rolloverTable.put(b, b.isRolloverEnabled() ? Boolean.TRUE : Boolean.FALSE);
            b.setRolloverEnabled(false);
        }
    }
    
    protected void setBorderToNormal(Component c) {
        if (c instanceof AbstractButton) {
            AbstractButton b = (AbstractButton)(AbstractButton)c;
            Border border = (Border)(Border)borderTable.remove(b);
            b.setBorder(border);
            Boolean value = (Boolean)(Boolean)rolloverTable.remove(b);
            if (value != null) {
                b.setRolloverEnabled(value.booleanValue());
            }
        }
    }
    
    public void setFloatingLocation(int x, int y) {
        floatingX = x;
        floatingY = y;
    }
    
    public boolean isFloating() {
        return floating;
    }
    
    public void setFloating(boolean b, Point p) {
        if (toolBar.isFloatable() == true) {
            if (dragWindow != null) dragWindow.setVisible(false);
            this.floating = b;
            if (b == true) {
                if (dockingSource == null) {
                    dockingSource = toolBar.getParent();
                    dockingSource.remove(toolBar);
                }
                constraintBeforeFloating = calculateConstraint();
                if (propertyListener != null) UIManager.addPropertyChangeListener(propertyListener);
                if (floatingToolBar == null) floatingToolBar = createFloatingWindow(toolBar);
                floatingToolBar.getContentPane().add(toolBar, BorderLayout.CENTER);
                if (floatingToolBar instanceof Window) ((Window)(Window)floatingToolBar).pack();
                if (floatingToolBar instanceof Window) ((Window)(Window)floatingToolBar).setLocation(floatingX, floatingY);
                if (floatingToolBar instanceof Window) ((Window)(Window)floatingToolBar).show();
            } else {
                if (floatingToolBar == null) floatingToolBar = createFloatingWindow(toolBar);
                if (floatingToolBar instanceof Window) ((Window)(Window)floatingToolBar).setVisible(false);
                floatingToolBar.getContentPane().remove(toolBar);
                String constraint = getDockingConstraint(dockingSource, p);
                if (constraint == null) {
                    constraint = BorderLayout.NORTH;
                }
                int orientation = mapConstraintToOrientation(constraint);
                setOrientation(orientation);
                if (dockingSource == null) dockingSource = toolBar.getParent();
                if (propertyListener != null) UIManager.removePropertyChangeListener(propertyListener);
                dockingSource.add(constraint, toolBar);
            }
            dockingSource.invalidate();
            Container dockingSourceParent = dockingSource.getParent();
            if (dockingSourceParent != null) dockingSourceParent.validate();
            dockingSource.repaint();
        }
    }
    
    private int mapConstraintToOrientation(String constraint) {
        int orientation = toolBar.getOrientation();
        if (constraint != null) {
            if (constraint.equals(BorderLayout.EAST) || constraint.equals(BorderLayout.WEST)) orientation = JToolBar.VERTICAL; else if (constraint.equals(BorderLayout.NORTH) || constraint.equals(BorderLayout.SOUTH)) orientation = JToolBar.HORIZONTAL;
        }
        return orientation;
    }
    
    public void setOrientation(int orientation) {
        toolBar.setOrientation(orientation);
        if (dragWindow != null) dragWindow.setOrientation(orientation);
    }
    
    public Color getDockingColor() {
        return dockingColor;
    }
    
    public void setDockingColor(Color c) {
        this.dockingColor = c;
    }
    
    public Color getFloatingColor() {
        return floatingColor;
    }
    
    public void setFloatingColor(Color c) {
        this.floatingColor = c;
    }
    
    private boolean isBlocked(Component comp, Object constraint) {
        if (comp instanceof Container) {
            Container cont = (Container)(Container)comp;
            LayoutManager lm = cont.getLayout();
            if (lm instanceof BorderLayout) {
                BorderLayout blm = (BorderLayout)(BorderLayout)lm;
                Component c = blm.getLayoutComponent(cont, constraint);
                return (c != null && c != toolBar);
            }
        }
        return false;
    }
    
    public boolean canDock(Component c, Point p) {
        return (p != null && getDockingConstraint(c, p) != null);
    }
    
    private String calculateConstraint() {
        String constraint = null;
        LayoutManager lm = dockingSource.getLayout();
        if (lm instanceof BorderLayout) {
            constraint = (String)(String)((BorderLayout)(BorderLayout)lm).getConstraints(toolBar);
        }
        return (constraint != null) ? constraint : constraintBeforeFloating;
    }
    
    private String getDockingConstraint(Component c, Point p) {
        if (p == null) return constraintBeforeFloating;
        if (c.contains(p)) {
            dockingSensitivity = (toolBar.getOrientation() == JToolBar.HORIZONTAL) ? toolBar.getSize().height : toolBar.getSize().width;
            if (p.y < dockingSensitivity && !isBlocked(c, BorderLayout.NORTH)) {
                return BorderLayout.NORTH;
            }
            if (p.x >= c.getWidth() - dockingSensitivity && !isBlocked(c, BorderLayout.EAST)) {
                return BorderLayout.EAST;
            }
            if (p.x < dockingSensitivity && !isBlocked(c, BorderLayout.WEST)) {
                return BorderLayout.WEST;
            }
            if (p.y >= c.getHeight() - dockingSensitivity && !isBlocked(c, BorderLayout.SOUTH)) {
                return BorderLayout.SOUTH;
            }
        }
        return null;
    }
    
    protected void dragTo(Point position, Point origin) {
        if (toolBar.isFloatable() == true) {
            try {
                if (dragWindow == null) dragWindow = createDragWindow(toolBar);
                Point offset = dragWindow.getOffset();
                if (offset == null) {
                    Dimension size = toolBar.getPreferredSize();
                    offset = new Point(size.width / 2, size.height / 2);
                    dragWindow.setOffset(offset);
                }
                Point global = new Point(origin.x + position.x, origin.y + position.y);
                Point dragPoint = new Point(global.x - offset.x, global.y - offset.y);
                if (dockingSource == null) dockingSource = toolBar.getParent();
                constraintBeforeFloating = calculateConstraint();
                Point dockingPosition = dockingSource.getLocationOnScreen();
                Point comparisonPoint = new Point(global.x - dockingPosition.x, global.y - dockingPosition.y);
                if (canDock(dockingSource, comparisonPoint)) {
                    dragWindow.setBackground(getDockingColor());
                    String constraint = getDockingConstraint(dockingSource, comparisonPoint);
                    int orientation = mapConstraintToOrientation(constraint);
                    dragWindow.setOrientation(orientation);
                    dragWindow.setBorderColor(dockingBorderColor);
                } else {
                    dragWindow.setBackground(getFloatingColor());
                    dragWindow.setBorderColor(floatingBorderColor);
                }
                dragWindow.setLocation(dragPoint.x, dragPoint.y);
                if (dragWindow.isVisible() == false) {
                    Dimension size = toolBar.getPreferredSize();
                    dragWindow.setSize(size.width, size.height);
                    dragWindow.show();
                }
            } catch (IllegalComponentStateException e) {
            }
        }
    }
    
    protected void floatAt(Point position, Point origin) {
        if (toolBar.isFloatable() == true) {
            try {
                Point offset = dragWindow.getOffset();
                if (offset == null) {
                    offset = position;
                    dragWindow.setOffset(offset);
                }
                Point global = new Point(origin.x + position.x, origin.y + position.y);
                setFloatingLocation(global.x - offset.x, global.y - offset.y);
                if (dockingSource != null) {
                    Point dockingPosition = dockingSource.getLocationOnScreen();
                    Point comparisonPoint = new Point(global.x - dockingPosition.x, global.y - dockingPosition.y);
                    if (canDock(dockingSource, comparisonPoint)) {
                        setFloating(false, comparisonPoint);
                    } else {
                        setFloating(true, null);
                    }
                } else {
                    setFloating(true, null);
                }
                dragWindow.setOffset(null);
            } catch (IllegalComponentStateException e) {
            }
        }
    }
    
    private BasicToolBarUI$Handler getHandler() {
        if (handler == null) {
            handler = new BasicToolBarUI$Handler(this, null);
        }
        return handler;
    }
    
    protected ContainerListener createToolBarContListener() {
        return getHandler();
    }
    
    protected FocusListener createToolBarFocusListener() {
        return getHandler();
    }
    
    protected PropertyChangeListener createPropertyListener() {
        return getHandler();
    }
    
    protected MouseInputListener createDockingListener() {
        getHandler().tb = toolBar;
        return getHandler();
    }
    
    protected WindowListener createFrameListener() {
        return new BasicToolBarUI$FrameListener(this);
    }
    
    protected void paintDragWindow(Graphics g) {
        g.setColor(dragWindow.getBackground());
        int w = dragWindow.getWidth();
        int h = dragWindow.getHeight();
        g.fillRect(0, 0, w, h);
        g.setColor(dragWindow.getBorderColor());
        g.drawRect(0, 0, w - 1, h - 1);
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
}
