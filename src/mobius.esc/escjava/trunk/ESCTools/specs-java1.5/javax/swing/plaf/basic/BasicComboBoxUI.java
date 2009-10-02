package javax.swing.plaf.basic;

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.accessibility.*;
import javax.swing.plaf.*;
import javax.swing.border.*;
import javax.swing.text.*;
import javax.swing.event.*;
import java.beans.PropertyChangeListener;
import sun.awt.AppContext;
import sun.swing.DefaultLookup;

public class BasicComboBoxUI extends ComboBoxUI {
    
    /*synthetic*/ static long access$800(BasicComboBoxUI x0) {
        return x0.timeFactor;
    }
    
    /*synthetic*/ static long access$702(BasicComboBoxUI x0, long x1) {
        return x0.time = x1;
    }
    
    /*synthetic*/ static long access$700(BasicComboBoxUI x0) {
        return x0.time;
    }
    
    /*synthetic*/ static long access$602(BasicComboBoxUI x0, long x1) {
        return x0.lastTime = x1;
    }
    
    /*synthetic*/ static long access$600(BasicComboBoxUI x0) {
        return x0.lastTime;
    }
    
    /*synthetic*/ static boolean access$500(BasicComboBoxUI x0, int x1, int x2) {
        return x0.isNavigationKey(x1, x2);
    }
    
    /*synthetic*/ static boolean access$402(BasicComboBoxUI x0, boolean x1) {
        return x0.isTableCellEditor = x1;
    }
    
    /*synthetic*/ static void access$300(BasicComboBoxUI x0) {
        x0.updateToolTipTextForChildren();
    }
    
    /*synthetic*/ static boolean access$202(BasicComboBoxUI x0, boolean x1) {
        return x0.isDisplaySizeDirty = x1;
    }
    
    /*synthetic*/ static BasicComboBoxUI$Handler access$100(BasicComboBoxUI x0) {
        return x0.getHandler();
    }
    {
    }
    
    public BasicComboBoxUI() {
        
    }
    protected JComboBox comboBox;
    protected boolean hasFocus = false;
    private boolean isTableCellEditor = false;
    private static final String IS_TABLE_CELL_EDITOR = "JComboBox.isTableCellEditor";
    protected JList listBox;
    protected CellRendererPane currentValuePane = new CellRendererPane();
    protected ComboPopup popup;
    protected Component editor;
    protected JButton arrowButton;
    protected KeyListener keyListener;
    protected FocusListener focusListener;
    protected PropertyChangeListener propertyChangeListener;
    protected ItemListener itemListener;
    protected MouseListener popupMouseListener;
    protected MouseMotionListener popupMouseMotionListener;
    protected KeyListener popupKeyListener;
    protected ListDataListener listDataListener;
    private BasicComboBoxUI$Handler handler;
    private long timeFactor = 1000L;
    private long lastTime = 0L;
    private long time = 0L;
    JComboBox$KeySelectionManager keySelectionManager;
    protected boolean isMinimumSizeDirty = true;
    protected Dimension cachedMinimumSize = new Dimension(0, 0);
    private boolean isDisplaySizeDirty = true;
    private Dimension cachedDisplaySize = new Dimension(0, 0);
    private static final Object COMBO_UI_LIST_CELL_RENDERER_KEY = new StringBuffer("DefaultListCellRendererKey");
    static final StringBuffer HIDE_POPUP_KEY = new StringBuffer("HidePopupKey");
    
    private static ListCellRenderer getDefaultListCellRenderer() {
        ListCellRenderer renderer = (ListCellRenderer)(ListCellRenderer)AppContext.getAppContext().get(COMBO_UI_LIST_CELL_RENDERER_KEY);
        if (renderer == null) {
            renderer = new DefaultListCellRenderer();
            AppContext.getAppContext().put(COMBO_UI_LIST_CELL_RENDERER_KEY, new DefaultListCellRenderer());
        }
        return renderer;
    }
    
    static void loadActionMap(LazyActionMap map) {
        map.put(new BasicComboBoxUI$Actions("hidePopup"));
        map.put(new BasicComboBoxUI$Actions("pageDownPassThrough"));
        map.put(new BasicComboBoxUI$Actions("pageUpPassThrough"));
        map.put(new BasicComboBoxUI$Actions("homePassThrough"));
        map.put(new BasicComboBoxUI$Actions("endPassThrough"));
        map.put(new BasicComboBoxUI$Actions("selectNext"));
        map.put(new BasicComboBoxUI$Actions("selectNext2"));
        map.put(new BasicComboBoxUI$Actions("togglePopup"));
        map.put(new BasicComboBoxUI$Actions("spacePopup"));
        map.put(new BasicComboBoxUI$Actions("selectPrevious"));
        map.put(new BasicComboBoxUI$Actions("selectPrevious2"));
        map.put(new BasicComboBoxUI$Actions("enterPressed"));
    }
    
    public static ComponentUI createUI(JComponent c) {
        return new BasicComboBoxUI();
    }
    
    public void installUI(JComponent c) {
        isMinimumSizeDirty = true;
        comboBox = (JComboBox)(JComboBox)c;
        installDefaults();
        popup = createPopup();
        listBox = popup.getList();
        Boolean inTable = (Boolean)(Boolean)c.getClientProperty(IS_TABLE_CELL_EDITOR);
        if (inTable != null) {
            isTableCellEditor = inTable.equals(Boolean.TRUE) ? true : false;
        }
        if (comboBox.getRenderer() == null || comboBox.getRenderer() instanceof UIResource) {
            comboBox.setRenderer(createRenderer());
        }
        if (comboBox.getEditor() == null || comboBox.getEditor() instanceof UIResource) {
            comboBox.setEditor(createEditor());
        }
        installListeners();
        installComponents();
        comboBox.setLayout(createLayoutManager());
        comboBox.setRequestFocusEnabled(true);
        installKeyboardActions();
        comboBox.putClientProperty("doNotCancelPopup", HIDE_POPUP_KEY);
        if (keySelectionManager == null || keySelectionManager instanceof UIResource) {
            keySelectionManager = new BasicComboBoxUI$DefaultKeySelectionManager(this);
        }
        comboBox.setKeySelectionManager(keySelectionManager);
    }
    
    public void uninstallUI(JComponent c) {
        setPopupVisible(comboBox, false);
        popup.uninstallingUI();
        uninstallKeyboardActions();
        comboBox.setLayout(null);
        uninstallComponents();
        uninstallListeners();
        uninstallDefaults();
        if (comboBox.getRenderer() == null || comboBox.getRenderer() instanceof UIResource) {
            comboBox.setRenderer(null);
        }
        if (comboBox.getEditor() == null || comboBox.getEditor() instanceof UIResource) {
            if (comboBox.getEditor().getEditorComponent().hasFocus()) {
                comboBox.requestFocusInWindow();
            }
            comboBox.setEditor(null);
        }
        if (keySelectionManager instanceof UIResource) {
            comboBox.setKeySelectionManager(null);
        }
        handler = null;
        keyListener = null;
        focusListener = null;
        listDataListener = null;
        propertyChangeListener = null;
        popup = null;
        listBox = null;
        comboBox = null;
    }
    
    protected void installDefaults() {
        LookAndFeel.installColorsAndFont(comboBox, "ComboBox.background", "ComboBox.foreground", "ComboBox.font");
        LookAndFeel.installBorder(comboBox, "ComboBox.border");
        LookAndFeel.installProperty(comboBox, "opaque", Boolean.TRUE);
        Long l = (Long)(Long)UIManager.get("ComboBox.timeFactor");
        timeFactor = (l != null) ? l.longValue() : 1000L;
    }
    
    protected void installListeners() {
        if ((itemListener = createItemListener()) != null) {
            comboBox.addItemListener(itemListener);
        }
        if ((propertyChangeListener = createPropertyChangeListener()) != null) {
            comboBox.addPropertyChangeListener(propertyChangeListener);
        }
        if ((keyListener = createKeyListener()) != null) {
            comboBox.addKeyListener(keyListener);
        }
        if ((focusListener = createFocusListener()) != null) {
            comboBox.addFocusListener(focusListener);
        }
        if ((popupMouseListener = popup.getMouseListener()) != null) {
            comboBox.addMouseListener(popupMouseListener);
        }
        if ((popupMouseMotionListener = popup.getMouseMotionListener()) != null) {
            comboBox.addMouseMotionListener(popupMouseMotionListener);
        }
        if ((popupKeyListener = popup.getKeyListener()) != null) {
            comboBox.addKeyListener(popupKeyListener);
        }
        if (comboBox.getModel() != null) {
            if ((listDataListener = createListDataListener()) != null) {
                comboBox.getModel().addListDataListener(listDataListener);
            }
        }
    }
    
    protected void uninstallDefaults() {
        LookAndFeel.installColorsAndFont(comboBox, "ComboBox.background", "ComboBox.foreground", "ComboBox.font");
        LookAndFeel.uninstallBorder(comboBox);
    }
    
    protected void uninstallListeners() {
        if (keyListener != null) {
            comboBox.removeKeyListener(keyListener);
        }
        if (itemListener != null) {
            comboBox.removeItemListener(itemListener);
        }
        if (propertyChangeListener != null) {
            comboBox.removePropertyChangeListener(propertyChangeListener);
        }
        if (focusListener != null) {
            comboBox.removeFocusListener(focusListener);
        }
        if (popupMouseListener != null) {
            comboBox.removeMouseListener(popupMouseListener);
        }
        if (popupMouseMotionListener != null) {
            comboBox.removeMouseMotionListener(popupMouseMotionListener);
        }
        if (popupKeyListener != null) {
            comboBox.removeKeyListener(popupKeyListener);
        }
        if (comboBox.getModel() != null) {
            if (listDataListener != null) {
                comboBox.getModel().removeListDataListener(listDataListener);
            }
        }
    }
    
    protected ComboPopup createPopup() {
        return new BasicComboPopup(comboBox);
    }
    
    protected KeyListener createKeyListener() {
        return getHandler();
    }
    
    protected FocusListener createFocusListener() {
        return getHandler();
    }
    
    protected ListDataListener createListDataListener() {
        return getHandler();
    }
    
    protected ItemListener createItemListener() {
        return null;
    }
    
    protected PropertyChangeListener createPropertyChangeListener() {
        return getHandler();
    }
    
    protected LayoutManager createLayoutManager() {
        return getHandler();
    }
    
    protected ListCellRenderer createRenderer() {
        return new BasicComboBoxRenderer$UIResource();
    }
    
    protected ComboBoxEditor createEditor() {
        return new BasicComboBoxEditor$UIResource();
    }
    
    private BasicComboBoxUI$Handler getHandler() {
        if (handler == null) {
            handler = new BasicComboBoxUI$Handler(this, null);
        }
        return handler;
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
    
    private void updateToolTipTextForChildren() {
        Component[] children = comboBox.getComponents();
        for (int i = 0; i < children.length; ++i) {
            if (children[i] instanceof JComponent) {
                ((JComponent)(JComponent)children[i]).setToolTipText(comboBox.getToolTipText());
            }
        }
    }
    {
    }
    
    protected void installComponents() {
        arrowButton = createArrowButton();
        comboBox.add(arrowButton);
        if (arrowButton != null) {
            configureArrowButton();
        }
        if (comboBox.isEditable()) {
            addEditor();
        }
        comboBox.add(currentValuePane);
    }
    
    protected void uninstallComponents() {
        if (arrowButton != null) {
            unconfigureArrowButton();
        }
        if (editor != null) {
            unconfigureEditor();
        }
        comboBox.removeAll();
        arrowButton = null;
    }
    
    public void addEditor() {
        removeEditor();
        editor = comboBox.getEditor().getEditorComponent();
        if (editor != null) {
            configureEditor();
            comboBox.add(editor);
            if (comboBox.isFocusOwner()) {
                editor.requestFocusInWindow();
            }
        }
    }
    
    public void removeEditor() {
        if (editor != null) {
            unconfigureEditor();
            comboBox.remove(editor);
            editor = null;
        }
    }
    
    protected void configureEditor() {
        editor.setEnabled(comboBox.isEnabled());
        editor.setFont(comboBox.getFont());
        if (focusListener != null) {
            editor.addFocusListener(focusListener);
        }
        editor.addFocusListener(getHandler());
        comboBox.getEditor().addActionListener(getHandler());
        if (editor instanceof JComponent) {
            ((JComponent)(JComponent)editor).putClientProperty("doNotCancelPopup", HIDE_POPUP_KEY);
            ((JComponent)(JComponent)editor).setInheritsPopupMenu(true);
        }
        comboBox.configureEditor(comboBox.getEditor(), comboBox.getSelectedItem());
    }
    
    protected void unconfigureEditor() {
        if (focusListener != null) {
            editor.removeFocusListener(focusListener);
        }
        editor.removeFocusListener(getHandler());
        comboBox.getEditor().removeActionListener(getHandler());
    }
    
    public void configureArrowButton() {
        if (arrowButton != null) {
            arrowButton.setEnabled(comboBox.isEnabled());
            arrowButton.setRequestFocusEnabled(false);
            arrowButton.addMouseListener(popup.getMouseListener());
            arrowButton.addMouseMotionListener(popup.getMouseMotionListener());
            arrowButton.resetKeyboardActions();
            arrowButton.putClientProperty("doNotCancelPopup", HIDE_POPUP_KEY);
            arrowButton.setInheritsPopupMenu(true);
        }
    }
    
    public void unconfigureArrowButton() {
        if (arrowButton != null) {
            arrowButton.removeMouseListener(popup.getMouseListener());
            arrowButton.removeMouseMotionListener(popup.getMouseMotionListener());
        }
    }
    
    protected JButton createArrowButton() {
        JButton button = new BasicArrowButton(BasicArrowButton.SOUTH, UIManager.getColor("ComboBox.buttonBackground"), UIManager.getColor("ComboBox.buttonShadow"), UIManager.getColor("ComboBox.buttonDarkShadow"), UIManager.getColor("ComboBox.buttonHighlight"));
        button.setName("ComboBox.arrowButton");
        return button;
    }
    
    public boolean isPopupVisible(JComboBox c) {
        return popup.isVisible();
    }
    
    public void setPopupVisible(JComboBox c, boolean v) {
        if (v) {
            popup.show();
        } else {
            popup.hide();
        }
    }
    
    public boolean isFocusTraversable(JComboBox c) {
        return !comboBox.isEditable();
    }
    
    public void paint(Graphics g, JComponent c) {
        hasFocus = comboBox.hasFocus();
        if (!comboBox.isEditable()) {
            Rectangle r = rectangleForCurrentValue();
            paintCurrentValueBackground(g, r, hasFocus);
            paintCurrentValue(g, r, hasFocus);
        }
    }
    
    public Dimension getPreferredSize(JComponent c) {
        return getMinimumSize(c);
    }
    
    public Dimension getMinimumSize(JComponent c) {
        if (!isMinimumSizeDirty) {
            return new Dimension(cachedMinimumSize);
        }
        Dimension size = getDisplaySize();
        Insets insets = getInsets();
        size.height += insets.top + insets.bottom;
        int buttonSize = size.height - (insets.top + insets.bottom);
        size.width += insets.left + insets.right + buttonSize;
        cachedMinimumSize.setSize(size.width, size.height);
        isMinimumSizeDirty = false;
        return new Dimension(size);
    }
    
    public Dimension getMaximumSize(JComponent c) {
        return new Dimension(Short.MAX_VALUE, Short.MAX_VALUE);
    }
    
    public int getAccessibleChildrenCount(JComponent c) {
        if (comboBox.isEditable()) {
            return 2;
        } else {
            return 1;
        }
    }
    
    public Accessible getAccessibleChild(JComponent c, int i) {
        switch (i) {
        case 0: 
            if (popup instanceof Accessible) {
                AccessibleContext ac = ((Accessible)(Accessible)popup).getAccessibleContext();
                ac.setAccessibleParent(comboBox);
                return (Accessible)(Accessible)popup;
            }
            break;
        
        case 1: 
            if (comboBox.isEditable() && (editor instanceof Accessible)) {
                AccessibleContext ac = ((Accessible)(Accessible)editor).getAccessibleContext();
                ac.setAccessibleParent(comboBox);
                return (Accessible)(Accessible)editor;
            }
            break;
        
        }
        return null;
    }
    
    protected boolean isNavigationKey(int keyCode) {
        return keyCode == KeyEvent.VK_UP || keyCode == KeyEvent.VK_DOWN || keyCode == KeyEvent.VK_KP_UP || keyCode == KeyEvent.VK_KP_DOWN;
    }
    
    private boolean isNavigationKey(int keyCode, int modifiers) {
        InputMap inputMap = comboBox.getInputMap(JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);
        KeyStroke key = KeyStroke.getKeyStroke(keyCode, modifiers);
        if (inputMap != null && inputMap.get(key) != null) {
            return true;
        }
        return false;
    }
    
    protected void selectNextPossibleValue() {
        int si;
        if (isTableCellEditor) {
            si = listBox.getSelectedIndex();
        } else {
            si = comboBox.getSelectedIndex();
        }
        if (si < comboBox.getModel().getSize() - 1) {
            if (isTableCellEditor) {
                listBox.setSelectedIndex(si + 1);
                listBox.ensureIndexIsVisible(si + 1);
            } else {
                comboBox.setSelectedIndex(si + 1);
            }
            comboBox.repaint();
        }
    }
    
    protected void selectPreviousPossibleValue() {
        int si;
        if (isTableCellEditor) {
            si = listBox.getSelectedIndex();
        } else {
            si = comboBox.getSelectedIndex();
        }
        if (si > 0) {
            if (isTableCellEditor) {
                listBox.setSelectedIndex(si - 1);
                listBox.ensureIndexIsVisible(si - 1);
            } else {
                comboBox.setSelectedIndex(si - 1);
            }
            comboBox.repaint();
        }
    }
    
    protected void toggleOpenClose() {
        setPopupVisible(comboBox, !isPopupVisible(comboBox));
    }
    
    protected Rectangle rectangleForCurrentValue() {
        int width = comboBox.getWidth();
        int height = comboBox.getHeight();
        Insets insets = getInsets();
        int buttonSize = height - (insets.top + insets.bottom);
        if (arrowButton != null) {
            buttonSize = arrowButton.getWidth();
        }
        if (BasicGraphicsUtils.isLeftToRight(comboBox)) {
            return new Rectangle(insets.left, insets.top, width - (insets.left + insets.right + buttonSize), height - (insets.top + insets.bottom));
        } else {
            return new Rectangle(insets.left + buttonSize, insets.top, width - (insets.left + insets.right + buttonSize), height - (insets.top + insets.bottom));
        }
    }
    
    protected Insets getInsets() {
        return comboBox.getInsets();
    }
    
    public void paintCurrentValue(Graphics g, Rectangle bounds, boolean hasFocus) {
        ListCellRenderer renderer = comboBox.getRenderer();
        Component c;
        if (hasFocus && !isPopupVisible(comboBox)) {
            c = renderer.getListCellRendererComponent(listBox, comboBox.getSelectedItem(), -1, true, false);
        } else {
            c = renderer.getListCellRendererComponent(listBox, comboBox.getSelectedItem(), -1, false, false);
            c.setBackground(UIManager.getColor("ComboBox.background"));
        }
        c.setFont(comboBox.getFont());
        if (hasFocus && !isPopupVisible(comboBox)) {
            c.setForeground(listBox.getSelectionForeground());
            c.setBackground(listBox.getSelectionBackground());
        } else {
            if (comboBox.isEnabled()) {
                c.setForeground(comboBox.getForeground());
                c.setBackground(comboBox.getBackground());
            } else {
                c.setForeground(DefaultLookup.getColor(comboBox, this, "ComboBox.disabledForeground", null));
                c.setBackground(DefaultLookup.getColor(comboBox, this, "ComboBox.disabledBackground", null));
            }
        }
        boolean shouldValidate = false;
        if (c instanceof JPanel) {
            shouldValidate = true;
        }
        currentValuePane.paintComponent(g, c, comboBox, bounds.x, bounds.y, bounds.width, bounds.height, shouldValidate);
    }
    
    public void paintCurrentValueBackground(Graphics g, Rectangle bounds, boolean hasFocus) {
        Color t = g.getColor();
        if (comboBox.isEnabled()) g.setColor(DefaultLookup.getColor(comboBox, this, "ComboBox.background", null)); else g.setColor(DefaultLookup.getColor(comboBox, this, "ComboBox.disabledBackground", null));
        g.fillRect(bounds.x, bounds.y, bounds.width, bounds.height);
        g.setColor(t);
    }
    
    void repaintCurrentValue() {
        Rectangle r = rectangleForCurrentValue();
        comboBox.repaint(r.x, r.y, r.width, r.height);
    }
    
    protected Dimension getDefaultSize() {
        Dimension d = getSizeForComponent(getDefaultListCellRenderer().getListCellRendererComponent(listBox, " ", -1, false, false));
        return new Dimension(d.width, d.height);
    }
    
    protected Dimension getDisplaySize() {
        if (!isDisplaySizeDirty) {
            return new Dimension(cachedDisplaySize);
        }
        Dimension result = new Dimension();
        ListCellRenderer renderer = comboBox.getRenderer();
        if (renderer == null) {
            renderer = new DefaultListCellRenderer();
        }
        Object prototypeValue = comboBox.getPrototypeDisplayValue();
        if (prototypeValue != null) {
            result = getSizeForComponent(renderer.getListCellRendererComponent(listBox, prototypeValue, -1, false, false));
        } else {
            ComboBoxModel model = comboBox.getModel();
            int modelSize = model.getSize();
            Dimension d;
            Component cpn;
            if (modelSize > 0) {
                for (int i = 0; i < modelSize; i++) {
                    d = getSizeForComponent(renderer.getListCellRendererComponent(listBox, model.getElementAt(i), -1, false, false));
                    result.width = Math.max(result.width, d.width);
                    result.height = Math.max(result.height, d.height);
                }
            } else {
                result = getDefaultSize();
                if (comboBox.isEditable()) {
                    result.width = 100;
                }
            }
        }
        if (comboBox.isEditable()) {
            Dimension d = editor.getPreferredSize();
            result.width = Math.max(result.width, d.width);
            result.height = Math.max(result.height, d.height);
        }
        cachedDisplaySize.setSize(result.width, result.height);
        isDisplaySizeDirty = false;
        return result;
    }
    
    private Dimension getSizeForComponent(Component comp) {
        currentValuePane.add(comp);
        comp.setFont(comboBox.getFont());
        Dimension d = comp.getPreferredSize();
        currentValuePane.remove(comp);
        return d;
    }
    
    protected void installKeyboardActions() {
        InputMap km = getInputMap(JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT);
        SwingUtilities.replaceUIInputMap(comboBox, JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT, km);
        LazyActionMap.installLazyActionMap(comboBox, BasicComboBoxUI.class, "ComboBox.actionMap");
    }
    
    InputMap getInputMap(int condition) {
        if (condition == JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT) {
            return (InputMap)(InputMap)DefaultLookup.get(comboBox, this, "ComboBox.ancestorInputMap");
        }
        return null;
    }
    
    boolean isTableCellEditor() {
        return isTableCellEditor;
    }
    
    protected void uninstallKeyboardActions() {
        SwingUtilities.replaceUIInputMap(comboBox, JComponent.WHEN_ANCESTOR_OF_FOCUSED_COMPONENT, null);
        SwingUtilities.replaceUIActionMap(comboBox, null);
    }
    {
    }
    {
    }
    {
    }
}
