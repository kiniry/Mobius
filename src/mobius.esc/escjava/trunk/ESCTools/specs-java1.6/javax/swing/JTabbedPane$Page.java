package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.util.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;
import java.io.Serializable;

class JTabbedPane$Page extends AccessibleContext implements Serializable, Accessible, AccessibleComponent {
    /*synthetic*/ final JTabbedPane this$0;
    String title;
    Color background;
    Color foreground;
    Icon icon;
    Icon disabledIcon;
    JTabbedPane parent;
    Component component;
    String tip;
    boolean enabled = true;
    boolean needsUIUpdate;
    int mnemonic = -1;
    int mnemonicIndex = -1;
    
    JTabbedPane$Page(/*synthetic*/ final JTabbedPane this$0, JTabbedPane parent, String title, Icon icon, Icon disabledIcon, Component component, String tip) {
        this.this$0 = this$0;
        
        this.title = title;
        this.icon = icon;
        this.disabledIcon = disabledIcon;
        this.parent = parent;
        this.setAccessibleParent(parent);
        this.component = component;
        this.tip = tip;
        if (component instanceof Accessible) {
            AccessibleContext ac;
            ac = ((Accessible)(Accessible)component).getAccessibleContext();
            if (ac != null) {
                ac.setAccessibleParent(this);
            }
        }
    }
    
    void setMnemonic(int mnemonic) {
        this.mnemonic = mnemonic;
        updateDisplayedMnemonicIndex();
    }
    
    int getMnemonic() {
        return mnemonic;
    }
    
    void setDisplayedMnemonicIndex(int mnemonicIndex) {
        if (this.mnemonicIndex != mnemonicIndex) {
            if (mnemonicIndex != -1 && (title == null || mnemonicIndex < 0 || mnemonicIndex >= title.length())) {
                throw new IllegalArgumentException("Invalid mnemonic index: " + mnemonicIndex);
            }
            this.mnemonicIndex = mnemonicIndex;
            JTabbedPane.access$000(this$0, "displayedMnemonicIndexAt", null, null);
        }
    }
    
    int getDisplayedMnemonicIndex() {
        return this.mnemonicIndex;
    }
    
    void updateDisplayedMnemonicIndex() {
        setDisplayedMnemonicIndex(SwingUtilities.findDisplayedMnemonicIndex(title, mnemonic));
    }
    
    public AccessibleContext getAccessibleContext() {
        return this;
    }
    
    public String getAccessibleName() {
        if (accessibleName != null) {
            return accessibleName;
        } else if (title != null) {
            return title;
        }
        return null;
    }
    
    public String getAccessibleDescription() {
        if (accessibleDescription != null) {
            return accessibleDescription;
        } else if (tip != null) {
            return tip;
        }
        return null;
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.PAGE_TAB;
    }
    
    public AccessibleStateSet getAccessibleStateSet() {
        AccessibleStateSet states;
        states = parent.getAccessibleContext().getAccessibleStateSet();
        states.add(AccessibleState.SELECTABLE);
        int i = parent.indexOfTab(title);
        if (i == parent.getSelectedIndex()) {
            states.add(AccessibleState.SELECTED);
        }
        return states;
    }
    
    public int getAccessibleIndexInParent() {
        return parent.indexOfTab(title);
    }
    
    public int getAccessibleChildrenCount() {
        if (component instanceof Accessible) {
            return 1;
        } else {
            return 0;
        }
    }
    
    public Accessible getAccessibleChild(int i) {
        if (component instanceof Accessible) {
            return (Accessible)(Accessible)component;
        } else {
            return null;
        }
    }
    
    public Locale getLocale() {
        return parent.getLocale();
    }
    
    public AccessibleComponent getAccessibleComponent() {
        return this;
    }
    
    public Color getBackground() {
        return background != null ? background : parent.getBackground();
    }
    
    public void setBackground(Color c) {
        background = c;
    }
    
    public Color getForeground() {
        return foreground != null ? foreground : parent.getForeground();
    }
    
    public void setForeground(Color c) {
        foreground = c;
    }
    
    public Cursor getCursor() {
        return parent.getCursor();
    }
    
    public void setCursor(Cursor c) {
        parent.setCursor(c);
    }
    
    public Font getFont() {
        return parent.getFont();
    }
    
    public void setFont(Font f) {
        parent.setFont(f);
    }
    
    public FontMetrics getFontMetrics(Font f) {
        return parent.getFontMetrics(f);
    }
    
    public boolean isEnabled() {
        return enabled;
    }
    
    public void setEnabled(boolean b) {
        enabled = b;
    }
    
    public boolean isVisible() {
        return parent.isVisible();
    }
    
    public void setVisible(boolean b) {
        parent.setVisible(b);
    }
    
    public boolean isShowing() {
        return parent.isShowing();
    }
    
    public boolean contains(Point p) {
        Rectangle r = getBounds();
        return r.contains(p);
    }
    
    public Point getLocationOnScreen() {
        Point parentLocation = parent.getLocationOnScreen();
        Point componentLocation = getLocation();
        componentLocation.translate(parentLocation.x, parentLocation.y);
        return componentLocation;
    }
    
    public Point getLocation() {
        Rectangle r = getBounds();
        return new Point(r.x, r.y);
    }
    
    public void setLocation(Point p) {
    }
    
    public Rectangle getBounds() {
        return parent.getUI().getTabBounds(parent, parent.indexOfTab(title));
    }
    
    public void setBounds(Rectangle r) {
    }
    
    public Dimension getSize() {
        Rectangle r = getBounds();
        return new Dimension(r.width, r.height);
    }
    
    public void setSize(Dimension d) {
    }
    
    public Accessible getAccessibleAt(Point p) {
        if (component instanceof Accessible) {
            return (Accessible)(Accessible)component;
        } else {
            return null;
        }
    }
    
    public boolean isFocusTraversable() {
        return false;
    }
    
    public void requestFocus() {
    }
    
    public void addFocusListener(FocusListener l) {
    }
    
    public void removeFocusListener(FocusListener l) {
    }
    
    public AccessibleIcon[] getAccessibleIcon() {
        AccessibleIcon accessibleIcon = null;
        if (enabled && icon instanceof ImageIcon) {
            AccessibleContext ac = ((ImageIcon)(ImageIcon)icon).getAccessibleContext();
            accessibleIcon = (AccessibleIcon)(AccessibleIcon)ac;
        } else if (!enabled && disabledIcon instanceof ImageIcon) {
            AccessibleContext ac = ((ImageIcon)(ImageIcon)disabledIcon).getAccessibleContext();
            accessibleIcon = (AccessibleIcon)(AccessibleIcon)ac;
        }
        if (accessibleIcon != null) {
            AccessibleIcon[] returnIcons = new AccessibleIcon[1];
            returnIcons[0] = accessibleIcon;
            return returnIcons;
        } else {
            return null;
        }
    }
}
