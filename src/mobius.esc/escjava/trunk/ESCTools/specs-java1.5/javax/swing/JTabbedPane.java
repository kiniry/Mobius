package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.util.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;
import java.io.Serializable;
import java.io.ObjectOutputStream;
import java.io.ObjectInputStream;
import java.io.IOException;

public class JTabbedPane extends JComponent implements Serializable, Accessible, SwingConstants {
    
    /*synthetic*/ static void access$000(JTabbedPane x0, String x1, Object x2, Object x3) {
        x0.firePropertyChange(x1, x2, x3);
    }
    public static final int WRAP_TAB_LAYOUT = 0;
    public static final int SCROLL_TAB_LAYOUT = 1;
    private static final String uiClassID = "TabbedPaneUI";
    protected int tabPlacement = TOP;
    private int tabLayoutPolicy;
    protected SingleSelectionModel model;
    private boolean haveRegistered;
    protected ChangeListener changeListener = null;
    Vector pages;
    protected transient ChangeEvent changeEvent = null;
    
    public JTabbedPane() {
        this(TOP, WRAP_TAB_LAYOUT);
    }
    
    public JTabbedPane(int tabPlacement) {
        this(tabPlacement, WRAP_TAB_LAYOUT);
    }
    
    public JTabbedPane(int tabPlacement, int tabLayoutPolicy) {
        
        setTabPlacement(tabPlacement);
        setTabLayoutPolicy(tabLayoutPolicy);
        pages = new Vector(1);
        setModel(new DefaultSingleSelectionModel());
        updateUI();
    }
    
    public TabbedPaneUI getUI() {
        return (TabbedPaneUI)(TabbedPaneUI)ui;
    }
    
    public void setUI(TabbedPaneUI ui) {
        super.setUI(ui);
        for (int i = 0; i < getTabCount(); i++) {
            Icon icon = ((JTabbedPane$Page)(JTabbedPane$Page)pages.elementAt(i)).disabledIcon;
            if (icon instanceof UIResource) {
                setDisabledIconAt(i, null);
            }
        }
    }
    
    public void updateUI() {
        setUI((TabbedPaneUI)(TabbedPaneUI)UIManager.getUI(this));
    }
    
    public String getUIClassID() {
        return uiClassID;
    }
    {
    }
    
    protected ChangeListener createChangeListener() {
        return new JTabbedPane$ModelListener(this);
    }
    
    public void addChangeListener(ChangeListener l) {
        listenerList.add(ChangeListener.class, l);
    }
    
    public void removeChangeListener(ChangeListener l) {
        listenerList.remove(ChangeListener.class, l);
    }
    
    public ChangeListener[] getChangeListeners() {
        return (ChangeListener[])(ChangeListener[])listenerList.getListeners(ChangeListener.class);
    }
    
    protected void fireStateChanged() {
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == ChangeListener.class) {
                if (changeEvent == null) changeEvent = new ChangeEvent(this);
                ((ChangeListener)(ChangeListener)listeners[i + 1]).stateChanged(changeEvent);
            }
        }
    }
    
    public SingleSelectionModel getModel() {
        return model;
    }
    
    public void setModel(SingleSelectionModel model) {
        SingleSelectionModel oldModel = getModel();
        if (oldModel != null) {
            oldModel.removeChangeListener(changeListener);
            changeListener = null;
        }
        this.model = model;
        if (model != null) {
            changeListener = createChangeListener();
            model.addChangeListener(changeListener);
        }
        firePropertyChange("model", oldModel, model);
        repaint();
    }
    
    public int getTabPlacement() {
        return tabPlacement;
    }
    
    public void setTabPlacement(int tabPlacement) {
        if (tabPlacement != TOP && tabPlacement != LEFT && tabPlacement != BOTTOM && tabPlacement != RIGHT) {
            throw new IllegalArgumentException("illegal tab placement: must be TOP, BOTTOM, LEFT, or RIGHT");
        }
        if (this.tabPlacement != tabPlacement) {
            int oldValue = this.tabPlacement;
            this.tabPlacement = tabPlacement;
            firePropertyChange("tabPlacement", oldValue, tabPlacement);
            revalidate();
            repaint();
        }
    }
    
    public int getTabLayoutPolicy() {
        return tabLayoutPolicy;
    }
    
    public void setTabLayoutPolicy(int tabLayoutPolicy) {
        if (tabLayoutPolicy != WRAP_TAB_LAYOUT && tabLayoutPolicy != SCROLL_TAB_LAYOUT) {
            throw new IllegalArgumentException("illegal tab layout policy: must be WRAP_TAB_LAYOUT or SCROLL_TAB_LAYOUT");
        }
        if (this.tabLayoutPolicy != tabLayoutPolicy) {
            int oldValue = this.tabLayoutPolicy;
            this.tabLayoutPolicy = tabLayoutPolicy;
            firePropertyChange("tabLayoutPolicy", oldValue, tabLayoutPolicy);
            revalidate();
            repaint();
        }
    }
    
    public int getSelectedIndex() {
        return model.getSelectedIndex();
    }
    
    public void setSelectedIndex(int index) {
        if (index != -1) {
            checkIndex(index);
        }
        setSelectedIndexImpl(index);
    }
    
    private void setSelectedIndexImpl(int index) {
        int oldIndex = model.getSelectedIndex();
        JTabbedPane$Page oldPage = null;
        JTabbedPane$Page newPage = null;
        if ((oldIndex >= 0) && (oldIndex != index)) {
            oldPage = (JTabbedPane$Page)(JTabbedPane$Page)pages.elementAt(oldIndex);
        }
        if ((index >= 0) && (oldIndex != index)) {
            newPage = (JTabbedPane$Page)(JTabbedPane$Page)pages.elementAt(index);
        }
        model.setSelectedIndex(index);
        String oldName = null;
        String newName = null;
        if (oldPage != null) {
            oldPage.firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, AccessibleState.SELECTED, null);
            AccessibleContext ac = oldPage.getAccessibleContext();
            if (ac != null) {
                oldName = ac.getAccessibleName();
            }
        }
        if (newPage != null) {
            newPage.firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, null, AccessibleState.SELECTED);
            AccessibleContext ac = newPage.getAccessibleContext();
            if (ac != null) {
                newName = ac.getAccessibleName();
            }
        }
        if (newName != null) {
            getAccessibleContext().firePropertyChange(AccessibleContext.ACCESSIBLE_NAME_PROPERTY, oldName, newName);
        }
    }
    
    public Component getSelectedComponent() {
        int index = getSelectedIndex();
        if (index == -1) {
            return null;
        }
        return getComponentAt(index);
    }
    
    public void setSelectedComponent(Component c) {
        int index = indexOfComponent(c);
        if (index != -1) {
            setSelectedIndex(index);
        } else {
            throw new IllegalArgumentException("component not found in tabbed pane");
        }
    }
    
    public void insertTab(String title, Icon icon, Component component, String tip, int index) {
        int newIndex = index;
        int removeIndex = indexOfComponent(component);
        if (component != null && removeIndex != -1) {
            removeTabAt(removeIndex);
            if (newIndex > removeIndex) {
                newIndex--;
            }
        }
        int selectedIndex = getSelectedIndex();
        pages.insertElementAt(new JTabbedPane$Page(this, this, title != null ? title : "", icon, null, component, tip), newIndex);
        if (component != null) {
            addImpl(component, null, -1);
            component.setVisible(false);
        }
        if (pages.size() == 1) {
            setSelectedIndex(0);
        }
        if (selectedIndex >= newIndex) {
            setSelectedIndex(selectedIndex + 1);
        }
        if (!haveRegistered && tip != null) {
            ToolTipManager.sharedInstance().registerComponent(this);
            haveRegistered = true;
        }
        if (accessibleContext != null) {
            accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_VISIBLE_DATA_PROPERTY, null, component);
        }
        revalidate();
        repaint();
    }
    
    public void addTab(String title, Icon icon, Component component, String tip) {
        insertTab(title, icon, component, tip, pages.size());
    }
    
    public void addTab(String title, Icon icon, Component component) {
        insertTab(title, icon, component, null, pages.size());
    }
    
    public void addTab(String title, Component component) {
        insertTab(title, null, component, null, pages.size());
    }
    
    public Component add(Component component) {
        if (!(component instanceof UIResource)) {
            addTab(component.getName(), component);
        } else {
            super.add(component);
        }
        return component;
    }
    
    public Component add(String title, Component component) {
        if (!(component instanceof UIResource)) {
            addTab(title, component);
        } else {
            super.add(title, component);
        }
        return component;
    }
    
    public Component add(Component component, int index) {
        if (!(component instanceof UIResource)) {
            insertTab(component.getName(), null, component, null, index == -1 ? getTabCount() : index);
        } else {
            super.add(component, index);
        }
        return component;
    }
    
    public void add(Component component, Object constraints) {
        if (!(component instanceof UIResource)) {
            if (constraints instanceof String) {
                addTab((String)(String)constraints, component);
            } else if (constraints instanceof Icon) {
                addTab(null, (Icon)(Icon)constraints, component);
            } else {
                add(component);
            }
        } else {
            super.add(component, constraints);
        }
    }
    
    public void add(Component component, Object constraints, int index) {
        if (!(component instanceof UIResource)) {
            Icon icon = constraints instanceof Icon ? (Icon)(Icon)constraints : null;
            String title = constraints instanceof String ? (String)(String)constraints : null;
            insertTab(title, icon, component, null, index == -1 ? getTabCount() : index);
        } else {
            super.add(component, constraints, index);
        }
    }
    
    public void removeTabAt(int index) {
        checkIndex(index);
        int tabCount = getTabCount();
        int selected = getSelectedIndex();
        if (selected >= (tabCount - 1)) {
            setSelectedIndexImpl(selected - 1);
        }
        Component component = getComponentAt(index);
        if (accessibleContext != null) {
            accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_VISIBLE_DATA_PROPERTY, component, null);
        }
        pages.removeElementAt(index);
        putClientProperty("__index_to_remove__", new Integer(index));
        if (component != null) {
            Component[] components = getComponents();
            for (int i = components.length; --i >= 0; ) {
                if (components[i] == component) {
                    super.remove(i);
                    component.setVisible(true);
                    break;
                }
            }
        }
        revalidate();
        repaint();
    }
    
    public void remove(Component component) {
        int index = indexOfComponent(component);
        if (index != -1) {
            removeTabAt(index);
        } else {
            Component[] children = getComponents();
            for (int i = 0; i < children.length; i++) {
                if (component == children[i]) {
                    super.remove(i);
                    break;
                }
            }
        }
    }
    
    public void remove(int index) {
        removeTabAt(index);
    }
    
    public void removeAll() {
        setSelectedIndexImpl(-1);
        int tabCount = getTabCount();
        while (tabCount-- > 0) {
            removeTabAt(tabCount);
        }
    }
    
    public int getTabCount() {
        return pages.size();
    }
    
    public int getTabRunCount() {
        if (ui != null) {
            return ((TabbedPaneUI)(TabbedPaneUI)ui).getTabRunCount(this);
        }
        return 0;
    }
    
    public String getTitleAt(int index) {
        return ((JTabbedPane$Page)(JTabbedPane$Page)pages.elementAt(index)).title;
    }
    
    public Icon getIconAt(int index) {
        return ((JTabbedPane$Page)(JTabbedPane$Page)pages.elementAt(index)).icon;
    }
    
    public Icon getDisabledIconAt(int index) {
        JTabbedPane$Page page = ((JTabbedPane$Page)(JTabbedPane$Page)pages.elementAt(index));
        if (page.disabledIcon == null) {
            page.disabledIcon = UIManager.getLookAndFeel().getDisabledIcon(this, page.icon);
        }
        return page.disabledIcon;
    }
    
    public String getToolTipTextAt(int index) {
        return ((JTabbedPane$Page)(JTabbedPane$Page)pages.elementAt(index)).tip;
    }
    
    public Color getBackgroundAt(int index) {
        return ((JTabbedPane$Page)(JTabbedPane$Page)pages.elementAt(index)).getBackground();
    }
    
    public Color getForegroundAt(int index) {
        return ((JTabbedPane$Page)(JTabbedPane$Page)pages.elementAt(index)).getForeground();
    }
    
    public boolean isEnabledAt(int index) {
        return ((JTabbedPane$Page)(JTabbedPane$Page)pages.elementAt(index)).isEnabled();
    }
    
    public Component getComponentAt(int index) {
        return ((JTabbedPane$Page)(JTabbedPane$Page)pages.elementAt(index)).component;
    }
    
    public int getMnemonicAt(int tabIndex) {
        checkIndex(tabIndex);
        JTabbedPane$Page page = (JTabbedPane$Page)(JTabbedPane$Page)pages.elementAt(tabIndex);
        return page.getMnemonic();
    }
    
    public int getDisplayedMnemonicIndexAt(int tabIndex) {
        checkIndex(tabIndex);
        JTabbedPane$Page page = (JTabbedPane$Page)(JTabbedPane$Page)pages.elementAt(tabIndex);
        return page.getDisplayedMnemonicIndex();
    }
    
    public Rectangle getBoundsAt(int index) {
        checkIndex(index);
        if (ui != null) {
            return ((TabbedPaneUI)(TabbedPaneUI)ui).getTabBounds(this, index);
        }
        return null;
    }
    
    public void setTitleAt(int index, String title) {
        JTabbedPane$Page page = (JTabbedPane$Page)(JTabbedPane$Page)pages.elementAt(index);
        String oldTitle = page.title;
        page.title = title;
        if (oldTitle != title) {
            firePropertyChange("indexForTitle", -1, index);
        }
        page.updateDisplayedMnemonicIndex();
        if ((oldTitle != title) && (accessibleContext != null)) {
            accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_VISIBLE_DATA_PROPERTY, oldTitle, title);
        }
        if (title == null || oldTitle == null || !title.equals(oldTitle)) {
            revalidate();
            repaint();
        }
    }
    
    public void setIconAt(int index, Icon icon) {
        JTabbedPane$Page page = (JTabbedPane$Page)(JTabbedPane$Page)pages.elementAt(index);
        Icon oldIcon = page.icon;
        if (icon != oldIcon) {
            page.icon = icon;
            if (page.disabledIcon instanceof UIResource) {
                page.disabledIcon = null;
            }
            if (accessibleContext != null) {
                accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_VISIBLE_DATA_PROPERTY, oldIcon, icon);
            }
            revalidate();
            repaint();
        }
    }
    
    public void setDisabledIconAt(int index, Icon disabledIcon) {
        Icon oldIcon = ((JTabbedPane$Page)(JTabbedPane$Page)pages.elementAt(index)).disabledIcon;
        ((JTabbedPane$Page)(JTabbedPane$Page)pages.elementAt(index)).disabledIcon = disabledIcon;
        if (disabledIcon != oldIcon && !isEnabledAt(index)) {
            revalidate();
            repaint();
        }
    }
    
    public void setToolTipTextAt(int index, String toolTipText) {
        String oldToolTipText = ((JTabbedPane$Page)(JTabbedPane$Page)pages.elementAt(index)).tip;
        ((JTabbedPane$Page)(JTabbedPane$Page)pages.elementAt(index)).tip = toolTipText;
        if ((oldToolTipText != toolTipText) && (accessibleContext != null)) {
            accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_VISIBLE_DATA_PROPERTY, oldToolTipText, toolTipText);
        }
        if (!haveRegistered && toolTipText != null) {
            ToolTipManager.sharedInstance().registerComponent(this);
            haveRegistered = true;
        }
    }
    
    public void setBackgroundAt(int index, Color background) {
        Color oldBg = ((JTabbedPane$Page)(JTabbedPane$Page)pages.elementAt(index)).background;
        ((JTabbedPane$Page)(JTabbedPane$Page)pages.elementAt(index)).setBackground(background);
        if (background == null || oldBg == null || !background.equals(oldBg)) {
            Rectangle tabBounds = getBoundsAt(index);
            if (tabBounds != null) {
                repaint(tabBounds);
            }
        }
    }
    
    public void setForegroundAt(int index, Color foreground) {
        Color oldFg = ((JTabbedPane$Page)(JTabbedPane$Page)pages.elementAt(index)).foreground;
        ((JTabbedPane$Page)(JTabbedPane$Page)pages.elementAt(index)).setForeground(foreground);
        if (foreground == null || oldFg == null || !foreground.equals(oldFg)) {
            Rectangle tabBounds = getBoundsAt(index);
            if (tabBounds != null) {
                repaint(tabBounds);
            }
        }
    }
    
    public void setEnabledAt(int index, boolean enabled) {
        boolean oldEnabled = ((JTabbedPane$Page)(JTabbedPane$Page)pages.elementAt(index)).isEnabled();
        ((JTabbedPane$Page)(JTabbedPane$Page)pages.elementAt(index)).setEnabled(enabled);
        if (enabled != oldEnabled) {
            revalidate();
            repaint();
        }
    }
    
    public void setComponentAt(int index, Component component) {
        JTabbedPane$Page page = (JTabbedPane$Page)(JTabbedPane$Page)pages.elementAt(index);
        if (component != page.component) {
            if (page.component != null) {
                synchronized (getTreeLock()) {
                    int count = getComponentCount();
                    Component[] children = getComponents();
                    for (int i = 0; i < count; i++) {
                        if (children[i] == page.component) {
                            super.remove(i);
                        }
                    }
                }
            }
            page.component = component;
            component.setVisible(getSelectedIndex() == index);
            addImpl(component, null, -1);
            revalidate();
        }
    }
    
    public void setDisplayedMnemonicIndexAt(int tabIndex, int mnemonicIndex) {
        checkIndex(tabIndex);
        JTabbedPane$Page page = (JTabbedPane$Page)(JTabbedPane$Page)pages.elementAt(tabIndex);
        page.setDisplayedMnemonicIndex(mnemonicIndex);
    }
    
    public void setMnemonicAt(int tabIndex, int mnemonic) {
        checkIndex(tabIndex);
        JTabbedPane$Page page = (JTabbedPane$Page)(JTabbedPane$Page)pages.elementAt(tabIndex);
        page.setMnemonic(mnemonic);
        firePropertyChange("mnemonicAt", null, null);
    }
    
    public int indexOfTab(String title) {
        for (int i = 0; i < getTabCount(); i++) {
            if (getTitleAt(i).equals(title == null ? "" : title)) {
                return i;
            }
        }
        return -1;
    }
    
    public int indexOfTab(Icon icon) {
        for (int i = 0; i < getTabCount(); i++) {
            Icon tabIcon = getIconAt(i);
            if ((tabIcon != null && tabIcon.equals(icon)) || (tabIcon == null && tabIcon == icon)) {
                return i;
            }
        }
        return -1;
    }
    
    public int indexOfComponent(Component component) {
        for (int i = 0; i < getTabCount(); i++) {
            Component c = getComponentAt(i);
            if ((c != null && c.equals(component)) || (c == null && c == component)) {
                return i;
            }
        }
        return -1;
    }
    
    public int indexAtLocation(int x, int y) {
        if (ui != null) {
            return ((TabbedPaneUI)(TabbedPaneUI)ui).tabForCoordinate(this, x, y);
        }
        return -1;
    }
    
    public String getToolTipText(MouseEvent event) {
        if (ui != null) {
            int index = ((TabbedPaneUI)(TabbedPaneUI)ui).tabForCoordinate(this, event.getX(), event.getY());
            if (index != -1) {
                return ((JTabbedPane$Page)(JTabbedPane$Page)pages.elementAt(index)).tip;
            }
        }
        return super.getToolTipText(event);
    }
    
    private void checkIndex(int index) {
        if (index < 0 || index >= pages.size()) {
            throw new IndexOutOfBoundsException("Index: " + index + ", Tab count: " + pages.size());
        }
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        if (getUIClassID().equals(uiClassID)) {
            byte count = JComponent.getWriteObjCounter(this);
            JComponent.setWriteObjCounter(this, --count);
            if (count == 0 && ui != null) {
                ui.installUI(this);
            }
        }
    }
    
    void compWriteObjectNotify() {
        super.compWriteObjectNotify();
        if (getToolTipText() == null && haveRegistered) {
            ToolTipManager.sharedInstance().unregisterComponent(this);
        }
    }
    
    private void readObject(ObjectInputStream s) throws IOException, ClassNotFoundException {
        s.defaultReadObject();
        if ((ui != null) && (getUIClassID().equals(uiClassID))) {
            ui.installUI(this);
        }
        if (getToolTipText() == null && haveRegistered) {
            ToolTipManager.sharedInstance().registerComponent(this);
        }
    }
    
    protected String paramString() {
        String tabPlacementString;
        if (tabPlacement == TOP) {
            tabPlacementString = "TOP";
        } else if (tabPlacement == BOTTOM) {
            tabPlacementString = "BOTTOM";
        } else if (tabPlacement == LEFT) {
            tabPlacementString = "LEFT";
        } else if (tabPlacement == RIGHT) {
            tabPlacementString = "RIGHT";
        } else tabPlacementString = "";
        String haveRegisteredString = (haveRegistered ? "true" : "false");
        return super.paramString() + ",haveRegistered=" + haveRegisteredString + ",tabPlacement=" + tabPlacementString;
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JTabbedPane$AccessibleJTabbedPane(this);
        }
        return accessibleContext;
    }
    {
    }
    {
    }
}
