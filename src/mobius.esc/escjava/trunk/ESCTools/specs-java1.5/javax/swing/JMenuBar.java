package javax.swing;

import java.awt.Component;
import java.awt.Graphics;
import java.awt.Insets;
import java.awt.event.*;
import java.util.Vector;
import java.io.Serializable;
import java.io.ObjectOutputStream;
import java.io.ObjectInputStream;
import java.io.IOException;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

public class JMenuBar extends JComponent implements Accessible, MenuElement {
    private static final String uiClassID = "MenuBarUI";
    private transient SingleSelectionModel selectionModel;
    private boolean paintBorder = true;
    private Insets margin = null;
    private static final boolean TRACE = false;
    private static final boolean VERBOSE = false;
    private static final boolean DEBUG = false;
    
    public JMenuBar() {
        
        setFocusTraversalKeysEnabled(false);
        setSelectionModel(new DefaultSingleSelectionModel());
        updateUI();
    }
    
    public MenuBarUI getUI() {
        return (MenuBarUI)(MenuBarUI)ui;
    }
    
    public void setUI(MenuBarUI ui) {
        super.setUI(ui);
    }
    
    public void updateUI() {
        setUI((MenuBarUI)(MenuBarUI)UIManager.getUI(this));
    }
    
    public String getUIClassID() {
        return uiClassID;
    }
    
    public SingleSelectionModel getSelectionModel() {
        return selectionModel;
    }
    
    public void setSelectionModel(SingleSelectionModel model) {
        SingleSelectionModel oldValue = selectionModel;
        this.selectionModel = model;
        firePropertyChange("selectionModel", oldValue, selectionModel);
    }
    
    public JMenu add(JMenu c) {
        super.add(c);
        return c;
    }
    
    public JMenu getMenu(int index) {
        Component c = getComponentAtIndex(index);
        if (c instanceof JMenu) return (JMenu)(JMenu)c;
        return null;
    }
    
    public int getMenuCount() {
        return getComponentCount();
    }
    
    public void setHelpMenu(JMenu menu) {
        throw new Error("setHelpMenu() not yet implemented.");
    }
    
    public JMenu getHelpMenu() {
        throw new Error("getHelpMenu() not yet implemented.");
    }
    
    
    public Component getComponentAtIndex(int i) {
        return getComponent(i);
    }
    
    public int getComponentIndex(Component c) {
        int ncomponents = this.getComponentCount();
        Component[] component = this.getComponents();
        for (int i = 0; i < ncomponents; i++) {
            Component comp = component[i];
            if (comp == c) return i;
        }
        return -1;
    }
    
    public void setSelected(Component sel) {
        SingleSelectionModel model = getSelectionModel();
        int index = getComponentIndex(sel);
        model.setSelectedIndex(index);
    }
    
    public boolean isSelected() {
        return selectionModel.isSelected();
    }
    
    public boolean isBorderPainted() {
        return paintBorder;
    }
    
    public void setBorderPainted(boolean b) {
        boolean oldValue = paintBorder;
        paintBorder = b;
        firePropertyChange("borderPainted", oldValue, paintBorder);
        if (b != oldValue) {
            revalidate();
            repaint();
        }
    }
    
    protected void paintBorder(Graphics g) {
        if (isBorderPainted()) {
            super.paintBorder(g);
        }
    }
    
    public void setMargin(Insets m) {
        Insets old = margin;
        this.margin = m;
        firePropertyChange("margin", old, m);
        if (old == null || !old.equals(m)) {
            revalidate();
            repaint();
        }
    }
    
    public Insets getMargin() {
        if (margin == null) {
            return new Insets(0, 0, 0, 0);
        } else {
            return margin;
        }
    }
    
    public void processMouseEvent(MouseEvent event, MenuElement[] path, MenuSelectionManager manager) {
    }
    
    public void processKeyEvent(KeyEvent e, MenuElement[] path, MenuSelectionManager manager) {
    }
    
    public void menuSelectionChanged(boolean isIncluded) {
    }
    
    public MenuElement[] getSubElements() {
        MenuElement[] result;
        Vector tmp = new Vector();
        int c = getComponentCount();
        int i;
        Component m;
        for (i = 0; i < c; i++) {
            m = getComponent(i);
            if (m instanceof MenuElement) tmp.addElement(m);
        }
        result = new MenuElement[tmp.size()];
        for (i = 0, c = tmp.size(); i < c; i++) result[i] = (MenuElement)(MenuElement)tmp.elementAt(i);
        return result;
    }
    
    public Component getComponent() {
        return this;
    }
    
    protected String paramString() {
        String paintBorderString = (paintBorder ? "true" : "false");
        String marginString = (margin != null ? margin.toString() : "");
        return super.paramString() + ",margin=" + marginString + ",paintBorder=" + paintBorderString;
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JMenuBar$AccessibleJMenuBar(this);
        }
        return accessibleContext;
    }
    {
    }
    
    protected boolean processKeyBinding(KeyStroke ks, KeyEvent e, int condition, boolean pressed) {
        boolean retValue = super.processKeyBinding(ks, e, condition, pressed);
        if (!retValue) {
            MenuElement[] subElements = getSubElements();
            for (int i = 0; i < subElements.length; i++) {
                if (processBindingForKeyStrokeRecursive(subElements[i], ks, e, condition, pressed)) {
                    return true;
                }
            }
        }
        return retValue;
    }
    
    static boolean processBindingForKeyStrokeRecursive(MenuElement elem, KeyStroke ks, KeyEvent e, int condition, boolean pressed) {
        if (elem == null) {
            return false;
        }
        Component c = elem.getComponent();
        if (c != null && c instanceof JComponent && ((JComponent)(JComponent)c).processKeyBinding(ks, e, condition, pressed)) {
            return true;
        }
        MenuElement[] subElements = elem.getSubElements();
        for (int i = 0; i < subElements.length; i++) {
            if (processBindingForKeyStrokeRecursive(subElements[i], ks, e, condition, pressed)) {
                return true;
            }
        }
        return false;
    }
    
    public void addNotify() {
        super.addNotify();
        KeyboardManager.getCurrentManager().registerMenuBar(this);
    }
    
    public void removeNotify() {
        super.removeNotify();
        KeyboardManager.getCurrentManager().unregisterMenuBar(this);
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
        Object[] kvData = new Object[4];
        int n = 0;
        if (selectionModel instanceof Serializable) {
            kvData[n++] = "selectionModel";
            kvData[n++] = selectionModel;
        }
        s.writeObject(kvData);
    }
    
    private void readObject(ObjectInputStream s) throws IOException, ClassNotFoundException {
        s.defaultReadObject();
        Object[] kvData = (Object[])((Object[])s.readObject());
        for (int i = 0; i < kvData.length; i += 2) {
            if (kvData[i] == null) {
                break;
            } else if (kvData[i].equals("selectionModel")) {
                selectionModel = (SingleSelectionModel)(SingleSelectionModel)kvData[i + 1];
            }
        }
    }
}
