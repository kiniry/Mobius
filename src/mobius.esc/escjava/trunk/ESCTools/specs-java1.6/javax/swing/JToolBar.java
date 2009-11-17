package javax.swing;

import java.awt.Component;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.Insets;
import java.awt.LayoutManager;
import java.awt.event.*;
import java.beans.*;
import javax.swing.plaf.*;
import javax.accessibility.*;
import java.io.ObjectOutputStream;
import java.io.IOException;

public class JToolBar extends JComponent implements SwingConstants, Accessible {
    private static final String uiClassID = "ToolBarUI";
    private boolean paintBorder = true;
    private Insets margin = null;
    private boolean floatable = true;
    private int orientation = HORIZONTAL;
    
    public JToolBar() {
        this(HORIZONTAL);
    }
    
    public JToolBar(int orientation) {
        this(null, orientation);
    }
    
    public JToolBar(String name) {
        this(name, HORIZONTAL);
    }
    
    public JToolBar(String name, int orientation) {
        
        setName(name);
        checkOrientation(orientation);
        this.orientation = orientation;
        JToolBar$DefaultToolBarLayout layout = new JToolBar$DefaultToolBarLayout(this, orientation);
        setLayout(layout);
        addPropertyChangeListener(layout);
        updateUI();
    }
    
    public ToolBarUI getUI() {
        return (ToolBarUI)(ToolBarUI)ui;
    }
    
    public void setUI(ToolBarUI ui) {
        super.setUI(ui);
    }
    
    public void updateUI() {
        setUI((ToolBarUI)(ToolBarUI)UIManager.getUI(this));
        if (getLayout() == null) {
            setLayout(new JToolBar$DefaultToolBarLayout(this, getOrientation()));
        }
        invalidate();
    }
    
    public String getUIClassID() {
        return uiClassID;
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
    
    public Component getComponentAtIndex(int i) {
        int ncomponents = this.getComponentCount();
        if (i >= 0 && i < ncomponents) {
            Component[] component = this.getComponents();
            return component[i];
        }
        return null;
    }
    
    public void setMargin(Insets m) {
        Insets old = margin;
        margin = m;
        firePropertyChange("margin", old, m);
        revalidate();
        repaint();
    }
    
    public Insets getMargin() {
        if (margin == null) {
            return new Insets(0, 0, 0, 0);
        } else {
            return margin;
        }
    }
    
    public boolean isBorderPainted() {
        return paintBorder;
    }
    
    public void setBorderPainted(boolean b) {
        if (paintBorder != b) {
            boolean old = paintBorder;
            paintBorder = b;
            firePropertyChange("borderPainted", old, b);
            revalidate();
            repaint();
        }
    }
    
    protected void paintBorder(Graphics g) {
        if (isBorderPainted()) {
            super.paintBorder(g);
        }
    }
    
    public boolean isFloatable() {
        return floatable;
    }
    
    public void setFloatable(boolean b) {
        if (floatable != b) {
            boolean old = floatable;
            floatable = b;
            firePropertyChange("floatable", old, b);
            revalidate();
            repaint();
        }
    }
    
    public int getOrientation() {
        return this.orientation;
    }
    
    public void setOrientation(int o) {
        checkOrientation(o);
        if (orientation != o) {
            int old = orientation;
            orientation = o;
            firePropertyChange("orientation", old, o);
            revalidate();
            repaint();
        }
    }
    
    public void setRollover(boolean rollover) {
        putClientProperty("JToolBar.isRollover", rollover ? Boolean.TRUE : Boolean.FALSE);
    }
    
    public boolean isRollover() {
        Boolean rollover = (Boolean)(Boolean)getClientProperty("JToolBar.isRollover");
        if (rollover != null) {
            return rollover.booleanValue();
        }
        return false;
    }
    
    private void checkOrientation(int orientation) {
        switch (orientation) {
        case VERTICAL: 
        
        case HORIZONTAL: 
            break;
        
        default: 
            throw new IllegalArgumentException("orientation must be one of: VERTICAL, HORIZONTAL");
        
        }
    }
    
    public void addSeparator() {
        addSeparator(null);
    }
    
    public void addSeparator(Dimension size) {
        JToolBar$Separator s = new JToolBar$Separator(size);
        add(s);
    }
    
    public JButton add(Action a) {
        JButton b = createActionComponent(a);
        b.setAction(a);
        add(b);
        return b;
    }
    
    protected JButton createActionComponent(Action a) {
        String text = a != null ? (String)(String)a.getValue(Action.NAME) : null;
        Icon icon = a != null ? (Icon)(Icon)a.getValue(Action.SMALL_ICON) : null;
        boolean enabled = a != null ? a.isEnabled() : true;
        String tooltip = a != null ? (String)(String)a.getValue(Action.SHORT_DESCRIPTION) : null;
        JButton b = new JToolBar$1(this, text, icon);
        if (icon != null) {
            b.putClientProperty("hideActionText", Boolean.TRUE);
        }
        b.setHorizontalTextPosition(JButton.CENTER);
        b.setVerticalTextPosition(JButton.BOTTOM);
        b.setEnabled(enabled);
        b.setToolTipText(tooltip);
        return b;
    }
    
    protected PropertyChangeListener createActionChangeListener(JButton b) {
        return null;
    }
    
    protected void addImpl(Component comp, Object constraints, int index) {
        if (comp instanceof JToolBar$Separator) {
            if (getOrientation() == VERTICAL) {
                ((JToolBar$Separator)(JToolBar$Separator)comp).setOrientation(JSeparator.HORIZONTAL);
            } else {
                ((JToolBar$Separator)(JToolBar$Separator)comp).setOrientation(JSeparator.VERTICAL);
            }
        }
        super.addImpl(comp, constraints, index);
        if (comp instanceof JButton) {
            ((JButton)(JButton)comp).setDefaultCapable(false);
        }
    }
    {
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
    
    protected String paramString() {
        String paintBorderString = (paintBorder ? "true" : "false");
        String marginString = (margin != null ? margin.toString() : "");
        String floatableString = (floatable ? "true" : "false");
        String orientationString = (orientation == HORIZONTAL ? "HORIZONTAL" : "VERTICAL");
        return super.paramString() + ",floatable=" + floatableString + ",margin=" + marginString + ",orientation=" + orientationString + ",paintBorder=" + paintBorderString;
    }
    {
    }
    
    public void setLayout(LayoutManager mgr) {
        LayoutManager oldMgr = getLayout();
        if (oldMgr instanceof PropertyChangeListener) {
            removePropertyChangeListener((PropertyChangeListener)(PropertyChangeListener)oldMgr);
        }
        super.setLayout(mgr);
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JToolBar$AccessibleJToolBar(this);
        }
        return accessibleContext;
    }
    {
    }
}
