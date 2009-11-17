package javax.swing.plaf.basic;

import sun.swing.DefaultLookup;
import javax.swing.*;
import javax.swing.border.Border;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.peer.ComponentPeer;
import java.awt.peer.LightweightPeer;
import java.beans.*;
import java.util.*;
import javax.swing.plaf.SplitPaneUI;
import javax.swing.plaf.ComponentUI;
import javax.swing.plaf.UIResource;

public class BasicSplitPaneUI extends SplitPaneUI {
    
    /*synthetic*/ static boolean access$600(BasicSplitPaneUI x0) {
        return x0.getKeepHidden();
    }
    
    /*synthetic*/ static boolean access$502(BasicSplitPaneUI x0, boolean x1) {
        return x0.dividerLocationIsSet = x1;
    }
    
    /*synthetic*/ static boolean access$500(BasicSplitPaneUI x0) {
        return x0.dividerLocationIsSet;
    }
    
    /*synthetic*/ static Color access$400(BasicSplitPaneUI x0) {
        return x0.dividerDraggingColor;
    }
    
    /*synthetic*/ static int access$302(BasicSplitPaneUI x0, int x1) {
        return x0.orientation = x1;
    }
    
    /*synthetic*/ static int access$300(BasicSplitPaneUI x0) {
        return x0.orientation;
    }
    
    /*synthetic*/ static boolean access$202(BasicSplitPaneUI x0, boolean x1) {
        return x0.dividerKeyboardResize = x1;
    }
    
    /*synthetic*/ static boolean access$200(BasicSplitPaneUI x0) {
        return x0.dividerKeyboardResize;
    }
    
    /*synthetic*/ static BasicSplitPaneUI$Handler access$100(BasicSplitPaneUI x0) {
        return x0.getHandler();
    }
    
    public BasicSplitPaneUI() {
        
    }
    protected static final String NON_CONTINUOUS_DIVIDER = "nonContinuousDivider";
    protected static int KEYBOARD_DIVIDER_MOVE_OFFSET = 3;
    protected JSplitPane splitPane;
    protected BasicSplitPaneUI$BasicHorizontalLayoutManager layoutManager;
    protected BasicSplitPaneDivider divider;
    protected PropertyChangeListener propertyChangeListener;
    protected FocusListener focusListener;
    private BasicSplitPaneUI$Handler handler;
    private static Set managingFocusForwardTraversalKeys;
    private static Set managingFocusBackwardTraversalKeys;
    protected int dividerSize;
    protected Component nonContinuousLayoutDivider;
    protected boolean draggingHW;
    protected int beginDragDividerLocation;
    
    protected KeyStroke upKey;
    
    protected KeyStroke downKey;
    
    protected KeyStroke leftKey;
    
    protected KeyStroke rightKey;
    
    protected KeyStroke homeKey;
    
    protected KeyStroke endKey;
    
    protected KeyStroke dividerResizeToggleKey;
    
    protected ActionListener keyboardUpLeftListener;
    
    protected ActionListener keyboardDownRightListener;
    
    protected ActionListener keyboardHomeListener;
    
    protected ActionListener keyboardEndListener;
    
    protected ActionListener keyboardResizeToggleListener;
    private int orientation;
    private int lastDragLocation;
    private boolean continuousLayout;
    private boolean dividerKeyboardResize;
    private boolean dividerLocationIsSet;
    private Color dividerDraggingColor;
    private boolean rememberPaneSizes;
    private boolean keepHidden = false;
    boolean painted;
    boolean ignoreDividerLocationChange;
    
    public static ComponentUI createUI(JComponent x) {
        return new BasicSplitPaneUI();
    }
    
    static void loadActionMap(LazyActionMap map) {
        map.put(new BasicSplitPaneUI$Actions("negativeIncrement"));
        map.put(new BasicSplitPaneUI$Actions("positiveIncrement"));
        map.put(new BasicSplitPaneUI$Actions("selectMin"));
        map.put(new BasicSplitPaneUI$Actions("selectMax"));
        map.put(new BasicSplitPaneUI$Actions("startResize"));
        map.put(new BasicSplitPaneUI$Actions("toggleFocus"));
        map.put(new BasicSplitPaneUI$Actions("focusOutForward"));
        map.put(new BasicSplitPaneUI$Actions("focusOutBackward"));
    }
    
    public void installUI(JComponent c) {
        splitPane = (JSplitPane)(JSplitPane)c;
        dividerLocationIsSet = false;
        dividerKeyboardResize = false;
        keepHidden = false;
        installDefaults();
        installListeners();
        installKeyboardActions();
        setLastDragLocation(-1);
    }
    
    protected void installDefaults() {
        LookAndFeel.installBorder(splitPane, "SplitPane.border");
        LookAndFeel.installColors(splitPane, "SplitPane.background", "SplitPane.foreground");
        LookAndFeel.installProperty(splitPane, "opaque", Boolean.TRUE);
        if (divider == null) divider = createDefaultDivider();
        divider.setBasicSplitPaneUI(this);
        Border b = divider.getBorder();
        if (b == null || !(b instanceof UIResource)) {
            divider.setBorder(UIManager.getBorder("SplitPaneDivider.border"));
        }
        dividerDraggingColor = UIManager.getColor("SplitPaneDivider.draggingColor");
        setOrientation(splitPane.getOrientation());
        LookAndFeel.installProperty(splitPane, "dividerSize", UIManager.get("SplitPane.dividerSize"));
        divider.setDividerSize(splitPane.getDividerSize());
        dividerSize = divider.getDividerSize();
        splitPane.add(divider, JSplitPane.DIVIDER);
        setContinuousLayout(splitPane.isContinuousLayout());
        resetLayoutManager();
        if (nonContinuousLayoutDivider == null) {
            setNonContinuousLayoutDivider(createDefaultNonContinuousLayoutDivider(), true);
        } else {
            setNonContinuousLayoutDivider(nonContinuousLayoutDivider, true);
        }
        if (managingFocusForwardTraversalKeys == null) {
            managingFocusForwardTraversalKeys = new TreeSet();
            managingFocusForwardTraversalKeys.add(KeyStroke.getKeyStroke(KeyEvent.VK_TAB, 0));
        }
        splitPane.setFocusTraversalKeys(KeyboardFocusManager.FORWARD_TRAVERSAL_KEYS, managingFocusForwardTraversalKeys);
        if (managingFocusBackwardTraversalKeys == null) {
            managingFocusBackwardTraversalKeys = new TreeSet();
            managingFocusBackwardTraversalKeys.add(KeyStroke.getKeyStroke(KeyEvent.VK_TAB, InputEvent.SHIFT_MASK));
        }
        splitPane.setFocusTraversalKeys(KeyboardFocusManager.BACKWARD_TRAVERSAL_KEYS, managingFocusBackwardTraversalKeys);
    }
    
    protected void installListeners() {
        if ((propertyChangeListener = createPropertyChangeListener()) != null) {
            splitPane.addPropertyChangeListener(propertyChangeListener);
        }
        if ((focusListener = createFocusListener()) != null) {
            splitPane.addFocusListener(focusListener);
        }
    }
    
    protected void installKeyboardActions() {
        InputMap km = getInputMap(JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);
        SwingUtilities.replaceUIInputMap(splitPane, JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT, km);
        LazyActionMap.installLazyActionMap(splitPane, BasicSplitPaneUI.class, "SplitPane.actionMap");
    }
    
    InputMap getInputMap(int condition) {
        if (condition == JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT) {
            return (InputMap)(InputMap)DefaultLookup.get(splitPane, this, "SplitPane.ancestorInputMap");
        }
        return null;
    }
    
    public void uninstallUI(JComponent c) {
        uninstallKeyboardActions();
        uninstallListeners();
        uninstallDefaults();
        dividerLocationIsSet = false;
        dividerKeyboardResize = false;
        splitPane = null;
    }
    
    protected void uninstallDefaults() {
        if (splitPane.getLayout() == layoutManager) {
            splitPane.setLayout(null);
        }
        if (nonContinuousLayoutDivider != null) {
            splitPane.remove(nonContinuousLayoutDivider);
        }
        LookAndFeel.uninstallBorder(splitPane);
        Border b = divider.getBorder();
        if (b instanceof UIResource) {
            divider.setBorder(null);
        }
        splitPane.remove(divider);
        divider.setBasicSplitPaneUI(null);
        layoutManager = null;
        divider = null;
        nonContinuousLayoutDivider = null;
        setNonContinuousLayoutDivider(null);
        splitPane.setFocusTraversalKeys(KeyboardFocusManager.FORWARD_TRAVERSAL_KEYS, null);
        splitPane.setFocusTraversalKeys(KeyboardFocusManager.BACKWARD_TRAVERSAL_KEYS, null);
    }
    
    protected void uninstallListeners() {
        if (propertyChangeListener != null) {
            splitPane.removePropertyChangeListener(propertyChangeListener);
            propertyChangeListener = null;
        }
        if (focusListener != null) {
            splitPane.removeFocusListener(focusListener);
            focusListener = null;
        }
        keyboardUpLeftListener = null;
        keyboardDownRightListener = null;
        keyboardHomeListener = null;
        keyboardEndListener = null;
        keyboardResizeToggleListener = null;
        handler = null;
    }
    
    protected void uninstallKeyboardActions() {
        SwingUtilities.replaceUIActionMap(splitPane, null);
        SwingUtilities.replaceUIInputMap(splitPane, JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT, null);
    }
    
    protected PropertyChangeListener createPropertyChangeListener() {
        return getHandler();
    }
    
    private BasicSplitPaneUI$Handler getHandler() {
        if (handler == null) {
            handler = new BasicSplitPaneUI$Handler(this, null);
        }
        return handler;
    }
    
    protected FocusListener createFocusListener() {
        return getHandler();
    }
    
    
    protected ActionListener createKeyboardUpLeftListener() {
        return new BasicSplitPaneUI$KeyboardUpLeftHandler(this);
    }
    
    
    protected ActionListener createKeyboardDownRightListener() {
        return new BasicSplitPaneUI$KeyboardDownRightHandler(this);
    }
    
    
    protected ActionListener createKeyboardHomeListener() {
        return new BasicSplitPaneUI$KeyboardHomeHandler(this);
    }
    
    
    protected ActionListener createKeyboardEndListener() {
        return new BasicSplitPaneUI$KeyboardEndHandler(this);
    }
    
    
    protected ActionListener createKeyboardResizeToggleListener() {
        return new BasicSplitPaneUI$KeyboardResizeToggleHandler(this);
    }
    
    public int getOrientation() {
        return orientation;
    }
    
    public void setOrientation(int orientation) {
        this.orientation = orientation;
    }
    
    public boolean isContinuousLayout() {
        return continuousLayout;
    }
    
    public void setContinuousLayout(boolean b) {
        continuousLayout = b;
    }
    
    public int getLastDragLocation() {
        return lastDragLocation;
    }
    
    public void setLastDragLocation(int l) {
        lastDragLocation = l;
    }
    
    int getKeyboardMoveIncrement() {
        return KEYBOARD_DIVIDER_MOVE_OFFSET;
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
    
    public BasicSplitPaneDivider getDivider() {
        return divider;
    }
    
    protected Component createDefaultNonContinuousLayoutDivider() {
        return new BasicSplitPaneUI$1(this);
    }
    
    protected void setNonContinuousLayoutDivider(Component newDivider) {
        setNonContinuousLayoutDivider(newDivider, true);
    }
    
    protected void setNonContinuousLayoutDivider(Component newDivider, boolean rememberSizes) {
        rememberPaneSizes = rememberSizes;
        if (nonContinuousLayoutDivider != null && splitPane != null) {
            splitPane.remove(nonContinuousLayoutDivider);
        }
        nonContinuousLayoutDivider = newDivider;
    }
    
    private void addHeavyweightDivider() {
        if (nonContinuousLayoutDivider != null && splitPane != null) {
            Component leftC = splitPane.getLeftComponent();
            Component rightC = splitPane.getRightComponent();
            int lastLocation = splitPane.getDividerLocation();
            if (leftC != null) splitPane.setLeftComponent(null);
            if (rightC != null) splitPane.setRightComponent(null);
            splitPane.remove(divider);
            splitPane.add(nonContinuousLayoutDivider, BasicSplitPaneUI.NON_CONTINUOUS_DIVIDER, splitPane.getComponentCount());
            splitPane.setLeftComponent(leftC);
            splitPane.setRightComponent(rightC);
            splitPane.add(divider, JSplitPane.DIVIDER);
            if (rememberPaneSizes) {
                splitPane.setDividerLocation(lastLocation);
            }
        }
    }
    
    public Component getNonContinuousLayoutDivider() {
        return nonContinuousLayoutDivider;
    }
    
    public JSplitPane getSplitPane() {
        return splitPane;
    }
    
    public BasicSplitPaneDivider createDefaultDivider() {
        return new BasicSplitPaneDivider(this);
    }
    
    public void resetToPreferredSizes(JSplitPane jc) {
        if (splitPane != null) {
            layoutManager.resetToPreferredSizes();
            splitPane.revalidate();
            splitPane.repaint();
        }
    }
    
    public void setDividerLocation(JSplitPane jc, int location) {
        if (!ignoreDividerLocationChange) {
            dividerLocationIsSet = true;
            splitPane.revalidate();
            splitPane.repaint();
            if (keepHidden) {
                Insets insets = splitPane.getInsets();
                int orientation = splitPane.getOrientation();
                if ((orientation == JSplitPane.VERTICAL_SPLIT && location != insets.top && location != splitPane.getHeight() - divider.getHeight() - insets.top) || (orientation == JSplitPane.HORIZONTAL_SPLIT && location != insets.left && location != splitPane.getWidth() - divider.getWidth() - insets.left)) {
                    setKeepHidden(false);
                }
            }
        } else {
            ignoreDividerLocationChange = false;
        }
    }
    
    public int getDividerLocation(JSplitPane jc) {
        if (orientation == JSplitPane.HORIZONTAL_SPLIT) return divider.getLocation().x;
        return divider.getLocation().y;
    }
    
    public int getMinimumDividerLocation(JSplitPane jc) {
        int minLoc = 0;
        Component leftC = splitPane.getLeftComponent();
        if ((leftC != null) && (leftC.isVisible())) {
            Insets insets = splitPane.getInsets();
            Dimension minSize = leftC.getMinimumSize();
            if (orientation == JSplitPane.HORIZONTAL_SPLIT) {
                minLoc = minSize.width;
            } else {
                minLoc = minSize.height;
            }
            if (insets != null) {
                if (orientation == JSplitPane.HORIZONTAL_SPLIT) {
                    minLoc += insets.left;
                } else {
                    minLoc += insets.top;
                }
            }
        }
        return minLoc;
    }
    
    public int getMaximumDividerLocation(JSplitPane jc) {
        Dimension splitPaneSize = splitPane.getSize();
        int maxLoc = 0;
        Component rightC = splitPane.getRightComponent();
        if (rightC != null) {
            Insets insets = splitPane.getInsets();
            Dimension minSize = new Dimension(0, 0);
            if (rightC.isVisible()) {
                minSize = rightC.getMinimumSize();
            }
            if (orientation == JSplitPane.HORIZONTAL_SPLIT) {
                maxLoc = splitPaneSize.width - minSize.width;
            } else {
                maxLoc = splitPaneSize.height - minSize.height;
            }
            maxLoc -= dividerSize;
            if (insets != null) {
                if (orientation == JSplitPane.HORIZONTAL_SPLIT) {
                    maxLoc -= insets.right;
                } else {
                    maxLoc -= insets.top;
                }
            }
        }
        return Math.max(getMinimumDividerLocation(splitPane), maxLoc);
    }
    
    public void finishedPaintingChildren(JSplitPane jc, Graphics g) {
        if (jc == splitPane && getLastDragLocation() != -1 && !isContinuousLayout() && !draggingHW) {
            Dimension size = splitPane.getSize();
            g.setColor(dividerDraggingColor);
            if (orientation == JSplitPane.HORIZONTAL_SPLIT) {
                g.fillRect(getLastDragLocation(), 0, dividerSize - 1, size.height - 1);
            } else {
                g.fillRect(0, lastDragLocation, size.width - 1, dividerSize - 1);
            }
        }
    }
    
    public void paint(Graphics g, JComponent jc) {
        if (!painted && splitPane.getDividerLocation() < 0) {
            ignoreDividerLocationChange = true;
            splitPane.setDividerLocation(getDividerLocation(splitPane));
        }
        painted = true;
    }
    
    public Dimension getPreferredSize(JComponent jc) {
        if (splitPane != null) return layoutManager.preferredLayoutSize(splitPane);
        return new Dimension(0, 0);
    }
    
    public Dimension getMinimumSize(JComponent jc) {
        if (splitPane != null) return layoutManager.minimumLayoutSize(splitPane);
        return new Dimension(0, 0);
    }
    
    public Dimension getMaximumSize(JComponent jc) {
        if (splitPane != null) return layoutManager.maximumLayoutSize(splitPane);
        return new Dimension(0, 0);
    }
    
    public Insets getInsets(JComponent jc) {
        return null;
    }
    
    protected void resetLayoutManager() {
        if (orientation == JSplitPane.HORIZONTAL_SPLIT) {
            layoutManager = new BasicSplitPaneUI$BasicHorizontalLayoutManager(this, 0);
        } else {
            layoutManager = new BasicSplitPaneUI$BasicHorizontalLayoutManager(this, 1);
        }
        splitPane.setLayout(layoutManager);
        layoutManager.updateComponents();
        splitPane.revalidate();
        splitPane.repaint();
    }
    
    void setKeepHidden(boolean keepHidden) {
        this.keepHidden = keepHidden;
    }
    
    private boolean getKeepHidden() {
        return keepHidden;
    }
    
    protected void startDragging() {
        Component leftC = splitPane.getLeftComponent();
        Component rightC = splitPane.getRightComponent();
        ComponentPeer cPeer;
        beginDragDividerLocation = getDividerLocation(splitPane);
        draggingHW = false;
        if (leftC != null && (cPeer = leftC.getPeer()) != null && !(cPeer instanceof LightweightPeer)) {
            draggingHW = true;
        } else if (rightC != null && (cPeer = rightC.getPeer()) != null && !(cPeer instanceof LightweightPeer)) {
            draggingHW = true;
        }
        if (orientation == JSplitPane.HORIZONTAL_SPLIT) {
            setLastDragLocation(divider.getBounds().x);
            dividerSize = divider.getSize().width;
            if (!isContinuousLayout() && draggingHW) {
                nonContinuousLayoutDivider.setBounds(getLastDragLocation(), 0, dividerSize, splitPane.getHeight());
                addHeavyweightDivider();
            }
        } else {
            setLastDragLocation(divider.getBounds().y);
            dividerSize = divider.getSize().height;
            if (!isContinuousLayout() && draggingHW) {
                nonContinuousLayoutDivider.setBounds(0, getLastDragLocation(), splitPane.getWidth(), dividerSize);
                addHeavyweightDivider();
            }
        }
    }
    
    protected void dragDividerTo(int location) {
        if (getLastDragLocation() != location) {
            if (isContinuousLayout()) {
                splitPane.setDividerLocation(location);
                setLastDragLocation(location);
            } else {
                int lastLoc = getLastDragLocation();
                setLastDragLocation(location);
                if (orientation == JSplitPane.HORIZONTAL_SPLIT) {
                    if (draggingHW) {
                        nonContinuousLayoutDivider.setLocation(getLastDragLocation(), 0);
                    } else {
                        int splitHeight = splitPane.getHeight();
                        splitPane.repaint(lastLoc, 0, dividerSize, splitHeight);
                        splitPane.repaint(location, 0, dividerSize, splitHeight);
                    }
                } else {
                    if (draggingHW) {
                        nonContinuousLayoutDivider.setLocation(0, getLastDragLocation());
                    } else {
                        int splitWidth = splitPane.getWidth();
                        splitPane.repaint(0, lastLoc, splitWidth, dividerSize);
                        splitPane.repaint(0, location, splitWidth, dividerSize);
                    }
                }
            }
        }
    }
    
    protected void finishDraggingTo(int location) {
        dragDividerTo(location);
        setLastDragLocation(-1);
        if (!isContinuousLayout()) {
            Component leftC = splitPane.getLeftComponent();
            Rectangle leftBounds = leftC.getBounds();
            if (draggingHW) {
                if (orientation == JSplitPane.HORIZONTAL_SPLIT) {
                    nonContinuousLayoutDivider.setLocation(-dividerSize, 0);
                } else {
                    nonContinuousLayoutDivider.setLocation(0, -dividerSize);
                }
                splitPane.remove(nonContinuousLayoutDivider);
            }
            splitPane.setDividerLocation(location);
        }
    }
    
    
    protected int getDividerBorderSize() {
        return 1;
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
