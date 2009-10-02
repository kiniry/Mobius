package javax.swing.plaf.basic;

import javax.accessibility.AccessibleContext;
import javax.swing.*;
import javax.swing.border.Border;
import javax.swing.border.LineBorder;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.beans.PropertyChangeListener;

public class BasicComboPopup extends JPopupMenu implements ComboPopup {
    
    /*synthetic*/ static void access$300(BasicComboPopup x0, int x1) {
        x0.setListSelection(x1);
    }
    
    /*synthetic*/ static BasicComboPopup$Handler access$200(BasicComboPopup x0) {
        return x0.getHandler();
    }
    {
    }
    {
    }
    static final ListModel EmptyListModel = new BasicComboPopup$EmptyListModelClass(null);
    private static Border LIST_BORDER = new LineBorder(Color.BLACK, 1);
    protected JComboBox comboBox;
    protected JList list;
    protected JScrollPane scroller;
    protected boolean valueIsAdjusting = false;
    private BasicComboPopup$Handler handler;
    protected MouseMotionListener mouseMotionListener;
    protected MouseListener mouseListener;
    protected KeyListener keyListener;
    protected ListSelectionListener listSelectionListener;
    protected MouseListener listMouseListener;
    protected MouseMotionListener listMouseMotionListener;
    protected PropertyChangeListener propertyChangeListener;
    protected ListDataListener listDataListener;
    protected ItemListener itemListener;
    protected Timer autoscrollTimer;
    protected boolean hasEntered = false;
    protected boolean isAutoScrolling = false;
    protected int scrollDirection = SCROLL_UP;
    protected static final int SCROLL_UP = 0;
    protected static final int SCROLL_DOWN = 1;
    
    public void show() {
        setListSelection(comboBox.getSelectedIndex());
        Point location = getPopupLocation();
        show(comboBox, location.x, location.y);
    }
    
    public void hide() {
        MenuSelectionManager manager = MenuSelectionManager.defaultManager();
        MenuElement[] selection = manager.getSelectedPath();
        for (int i = 0; i < selection.length; i++) {
            if (selection[i] == this) {
                manager.clearSelectedPath();
                break;
            }
        }
        if (selection.length > 0) {
            comboBox.repaint();
        }
    }
    
    public JList getList() {
        return list;
    }
    
    public MouseListener getMouseListener() {
        if (mouseListener == null) {
            mouseListener = createMouseListener();
        }
        return mouseListener;
    }
    
    public MouseMotionListener getMouseMotionListener() {
        if (mouseMotionListener == null) {
            mouseMotionListener = createMouseMotionListener();
        }
        return mouseMotionListener;
    }
    
    public KeyListener getKeyListener() {
        if (keyListener == null) {
            keyListener = createKeyListener();
        }
        return keyListener;
    }
    
    public void uninstallingUI() {
        if (propertyChangeListener != null) {
            comboBox.removePropertyChangeListener(propertyChangeListener);
        }
        if (itemListener != null) {
            comboBox.removeItemListener(itemListener);
        }
        uninstallComboBoxModelListeners(comboBox.getModel());
        uninstallKeyboardActions();
        uninstallListListeners();
        list.setModel(EmptyListModel);
    }
    
    protected void uninstallComboBoxModelListeners(ComboBoxModel model) {
        if (model != null && listDataListener != null) {
            model.removeListDataListener(listDataListener);
        }
    }
    
    protected void uninstallKeyboardActions() {
    }
    
    public BasicComboPopup(JComboBox combo) {
        
        setName("ComboPopup.popup");
        comboBox = combo;
        setLightWeightPopupEnabled(comboBox.isLightWeightPopupEnabled());
        list = createList();
        list.setName("ComboBox.list");
        configureList();
        scroller = createScroller();
        scroller.setName("ComboBox.scrollPane");
        configureScroller();
        configurePopup();
        installComboBoxListeners();
        installKeyboardActions();
    }
    
    protected void firePopupMenuWillBecomeVisible() {
        super.firePopupMenuWillBecomeVisible();
        comboBox.firePopupMenuWillBecomeVisible();
    }
    
    protected void firePopupMenuWillBecomeInvisible() {
        super.firePopupMenuWillBecomeInvisible();
        comboBox.firePopupMenuWillBecomeInvisible();
    }
    
    protected void firePopupMenuCanceled() {
        super.firePopupMenuCanceled();
        comboBox.firePopupMenuCanceled();
    }
    
    protected MouseListener createMouseListener() {
        return getHandler();
    }
    
    protected MouseMotionListener createMouseMotionListener() {
        return getHandler();
    }
    
    protected KeyListener createKeyListener() {
        return null;
    }
    
    protected ListSelectionListener createListSelectionListener() {
        return null;
    }
    
    protected ListDataListener createListDataListener() {
        return null;
    }
    
    protected MouseListener createListMouseListener() {
        return getHandler();
    }
    
    protected MouseMotionListener createListMouseMotionListener() {
        return getHandler();
    }
    
    protected PropertyChangeListener createPropertyChangeListener() {
        return getHandler();
    }
    
    protected ItemListener createItemListener() {
        return getHandler();
    }
    
    private BasicComboPopup$Handler getHandler() {
        if (handler == null) {
            handler = new BasicComboPopup$Handler(this, null);
        }
        return handler;
    }
    
    protected JList createList() {
        return new BasicComboPopup$1(this, comboBox.getModel());
    }
    
    protected void configureList() {
        list.setFont(comboBox.getFont());
        list.setForeground(comboBox.getForeground());
        list.setBackground(comboBox.getBackground());
        list.setSelectionForeground(UIManager.getColor("ComboBox.selectionForeground"));
        list.setSelectionBackground(UIManager.getColor("ComboBox.selectionBackground"));
        list.setBorder(null);
        list.setCellRenderer(comboBox.getRenderer());
        list.setFocusable(false);
        list.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
        setListSelection(comboBox.getSelectedIndex());
        installListListeners();
    }
    
    protected void installListListeners() {
        if ((listMouseListener = createListMouseListener()) != null) {
            list.addMouseListener(listMouseListener);
        }
        if ((listMouseMotionListener = createListMouseMotionListener()) != null) {
            list.addMouseMotionListener(listMouseMotionListener);
        }
        if ((listSelectionListener = createListSelectionListener()) != null) {
            list.addListSelectionListener(listSelectionListener);
        }
    }
    
    void uninstallListListeners() {
        if (listMouseListener != null) {
            list.removeMouseListener(listMouseListener);
            listMouseListener = null;
        }
        if (listMouseMotionListener != null) {
            list.removeMouseMotionListener(listMouseMotionListener);
            listMouseMotionListener = null;
        }
        if (listSelectionListener != null) {
            list.removeListSelectionListener(listSelectionListener);
            listSelectionListener = null;
        }
        handler = null;
    }
    
    protected JScrollPane createScroller() {
        JScrollPane sp = new JScrollPane(list, ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED, ScrollPaneConstants.HORIZONTAL_SCROLLBAR_NEVER);
        sp.setHorizontalScrollBar(null);
        return sp;
    }
    
    protected void configureScroller() {
        scroller.setFocusable(false);
        scroller.getVerticalScrollBar().setFocusable(false);
        scroller.setBorder(null);
    }
    
    protected void configurePopup() {
        setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));
        setBorderPainted(true);
        setBorder(LIST_BORDER);
        setOpaque(false);
        add(scroller);
        setDoubleBuffered(true);
        setFocusable(false);
    }
    
    protected void installComboBoxListeners() {
        if ((propertyChangeListener = createPropertyChangeListener()) != null) {
            comboBox.addPropertyChangeListener(propertyChangeListener);
        }
        if ((itemListener = createItemListener()) != null) {
            comboBox.addItemListener(itemListener);
        }
        installComboBoxModelListeners(comboBox.getModel());
    }
    
    protected void installComboBoxModelListeners(ComboBoxModel model) {
        if (model != null && (listDataListener = createListDataListener()) != null) {
            model.addListDataListener(listDataListener);
        }
    }
    
    protected void installKeyboardActions() {
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
    {
    }
    {
    }
    {
    }
    
    public boolean isFocusTraversable() {
        return false;
    }
    
    protected void startAutoScrolling(int direction) {
        if (isAutoScrolling) {
            autoscrollTimer.stop();
        }
        isAutoScrolling = true;
        if (direction == SCROLL_UP) {
            scrollDirection = SCROLL_UP;
            Point convertedPoint = SwingUtilities.convertPoint(scroller, new Point(1, 1), list);
            int top = list.locationToIndex(convertedPoint);
            list.setSelectedIndex(top);
            autoscrollTimer = new Timer(100, new BasicComboPopup$AutoScrollActionHandler(this, SCROLL_UP));
        } else if (direction == SCROLL_DOWN) {
            scrollDirection = SCROLL_DOWN;
            Dimension size = scroller.getSize();
            Point convertedPoint = SwingUtilities.convertPoint(scroller, new Point(1, (size.height - 1) - 2), list);
            int bottom = list.locationToIndex(convertedPoint);
            list.setSelectedIndex(bottom);
            autoscrollTimer = new Timer(100, new BasicComboPopup$AutoScrollActionHandler(this, SCROLL_DOWN));
        }
        autoscrollTimer.start();
    }
    
    protected void stopAutoScrolling() {
        isAutoScrolling = false;
        if (autoscrollTimer != null) {
            autoscrollTimer.stop();
            autoscrollTimer = null;
        }
    }
    
    protected void autoScrollUp() {
        int index = list.getSelectedIndex();
        if (index > 0) {
            list.setSelectedIndex(index - 1);
            list.ensureIndexIsVisible(index - 1);
        }
    }
    
    protected void autoScrollDown() {
        int index = list.getSelectedIndex();
        int lastItem = list.getModel().getSize() - 1;
        if (index < lastItem) {
            list.setSelectedIndex(index + 1);
            list.ensureIndexIsVisible(index + 1);
        }
    }
    
    public AccessibleContext getAccessibleContext() {
        AccessibleContext context = super.getAccessibleContext();
        context.setAccessibleParent(comboBox);
        return context;
    }
    
    protected void delegateFocus(MouseEvent e) {
        if (comboBox.isEditable()) {
            Component comp = comboBox.getEditor().getEditorComponent();
            if ((!(comp instanceof JComponent)) || ((JComponent)(JComponent)comp).isRequestFocusEnabled()) {
                comp.requestFocus();
            }
        } else if (comboBox.isRequestFocusEnabled()) {
            comboBox.requestFocus();
        }
    }
    
    protected void togglePopup() {
        if (isVisible()) {
            hide();
        } else {
            show();
        }
    }
    
    private void setListSelection(int selectedIndex) {
        if (selectedIndex == -1) {
            list.clearSelection();
        } else {
            list.setSelectedIndex(selectedIndex);
            list.ensureIndexIsVisible(selectedIndex);
        }
    }
    
    protected MouseEvent convertMouseEvent(MouseEvent e) {
        Point convertedPoint = SwingUtilities.convertPoint((Component)(Component)e.getSource(), e.getPoint(), list);
        MouseEvent newEvent = new MouseEvent((Component)(Component)e.getSource(), e.getID(), e.getWhen(), e.getModifiers(), convertedPoint.x, convertedPoint.y, e.getClickCount(), e.isPopupTrigger());
        return newEvent;
    }
    
    protected int getPopupHeightForRowCount(int maxRowCount) {
        int minRowCount = Math.min(maxRowCount, comboBox.getItemCount());
        int height = 0;
        ListCellRenderer renderer = list.getCellRenderer();
        Object value = null;
        for (int i = 0; i < minRowCount; ++i) {
            value = list.getModel().getElementAt(i);
            Component c = renderer.getListCellRendererComponent(list, value, i, false, false);
            height += c.getPreferredSize().height;
        }
        return height == 0 ? 100 : height;
    }
    
    protected Rectangle computePopupBounds(int px, int py, int pw, int ph) {
        Toolkit toolkit = Toolkit.getDefaultToolkit();
        Rectangle screenBounds;
        GraphicsConfiguration gc = comboBox.getGraphicsConfiguration();
        Point p = new Point();
        SwingUtilities.convertPointFromScreen(p, comboBox);
        if (gc != null) {
            Insets screenInsets = toolkit.getScreenInsets(gc);
            screenBounds = gc.getBounds();
            screenBounds.width -= (screenInsets.left + screenInsets.right);
            screenBounds.height -= (screenInsets.top + screenInsets.bottom);
            screenBounds.x += (p.x + screenInsets.left);
            screenBounds.y += (p.y + screenInsets.top);
        } else {
            screenBounds = new Rectangle(p, toolkit.getScreenSize());
        }
        Rectangle rect = new Rectangle(px, py, pw, ph);
        if (py + ph > screenBounds.y + screenBounds.height && ph < screenBounds.height) {
            rect.y = -rect.height;
        }
        return rect;
    }
    
    private Point getPopupLocation() {
        Dimension popupSize = comboBox.getSize();
        Insets insets = getInsets();
        popupSize.setSize(popupSize.width - (insets.right + insets.left), getPopupHeightForRowCount(comboBox.getMaximumRowCount()));
        Rectangle popupBounds = computePopupBounds(0, comboBox.getBounds().height, popupSize.width, popupSize.height);
        Dimension scrollSize = popupBounds.getSize();
        Point popupLocation = popupBounds.getLocation();
        scroller.setMaximumSize(scrollSize);
        scroller.setPreferredSize(scrollSize);
        scroller.setMinimumSize(scrollSize);
        list.revalidate();
        return popupLocation;
    }
    
    protected void updateListBoxSelectionForEvent(MouseEvent anEvent, boolean shouldScroll) {
        Point location = anEvent.getPoint();
        if (list == null) return;
        int index = list.locationToIndex(location);
        if (index == -1) {
            if (location.y < 0) index = 0; else index = comboBox.getModel().getSize() - 1;
        }
        if (list.getSelectedIndex() != index) {
            list.setSelectedIndex(index);
            if (shouldScroll) list.ensureIndexIsVisible(index);
        }
    }
}
