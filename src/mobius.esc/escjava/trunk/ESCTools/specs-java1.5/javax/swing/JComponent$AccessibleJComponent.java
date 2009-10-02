package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import javax.swing.border.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

public abstract class JComponent$AccessibleJComponent extends Container$AccessibleAWTContainer implements AccessibleExtendedComponent {
    /*synthetic*/ final JComponent this$0;
    
    protected JComponent$AccessibleJComponent(/*synthetic*/ final JComponent this$0) {
        this.this$0 = this$0;
        super(this$0);
    }
    protected ContainerListener accessibleContainerHandler = null;
    protected FocusListener accessibleFocusHandler = null;
    {
    }
    {
    }
    
    public void addPropertyChangeListener(PropertyChangeListener listener) {
        if (accessibleFocusHandler == null) {
            accessibleFocusHandler = new JComponent$AccessibleJComponent$AccessibleFocusHandler(this);
            this$0.addFocusListener(accessibleFocusHandler);
        }
        if (accessibleContainerHandler == null) {
            accessibleContainerHandler = new JComponent$AccessibleJComponent$AccessibleContainerHandler(this);
            this$0.addContainerListener(accessibleContainerHandler);
        }
        super.addPropertyChangeListener(listener);
    }
    
    public void removePropertyChangeListener(PropertyChangeListener listener) {
        if (accessibleFocusHandler != null) {
            this$0.removeFocusListener(accessibleFocusHandler);
            accessibleFocusHandler = null;
        }
        super.removePropertyChangeListener(listener);
    }
    
    protected String getBorderTitle(Border b) {
        String s;
        if (b instanceof TitledBorder) {
            return ((TitledBorder)(TitledBorder)b).getTitle();
        } else if (b instanceof CompoundBorder) {
            s = getBorderTitle(((CompoundBorder)(CompoundBorder)b).getInsideBorder());
            if (s == null) {
                s = getBorderTitle(((CompoundBorder)(CompoundBorder)b).getOutsideBorder());
            }
            return s;
        } else {
            return null;
        }
    }
    
    public String getAccessibleName() {
        String name = accessibleName;
        if (name == null) {
            name = getBorderTitle(this$0.getBorder());
        }
        if (name == null) {
            Object o = this$0.getClientProperty(JLabel.LABELED_BY_PROPERTY);
            if (o instanceof Accessible) {
                AccessibleContext ac = ((Accessible)(Accessible)o).getAccessibleContext();
                if (ac != null) {
                    name = ac.getAccessibleName();
                }
            }
        }
        return name;
    }
    
    public String getAccessibleDescription() {
        String description = accessibleDescription;
        if (description == null) {
            try {
                description = getToolTipText();
            } catch (Exception e) {
            }
        }
        if (description == null) {
            Object o = this$0.getClientProperty(JLabel.LABELED_BY_PROPERTY);
            if (o instanceof Accessible) {
                AccessibleContext ac = ((Accessible)(Accessible)o).getAccessibleContext();
                if (ac != null) {
                    description = ac.getAccessibleDescription();
                }
            }
        }
        return description;
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.SWING_COMPONENT;
    }
    
    public AccessibleStateSet getAccessibleStateSet() {
        AccessibleStateSet states = super.getAccessibleStateSet();
        if (this$0.isOpaque()) {
            states.add(AccessibleState.OPAQUE);
        }
        return states;
    }
    
    public int getAccessibleChildrenCount() {
        return super.getAccessibleChildrenCount();
    }
    
    public Accessible getAccessibleChild(int i) {
        return super.getAccessibleChild(i);
    }
    
    AccessibleExtendedComponent getAccessibleExtendedComponent() {
        return this;
    }
    
    public String getToolTipText() {
        return null;
    }
    
    public String getTitledBorderText() {
        Border border = this$0.getBorder();
        if (border instanceof TitledBorder) {
            return ((TitledBorder)(TitledBorder)border).getTitle();
        } else {
            return null;
        }
    }
    
    public AccessibleKeyBinding getAccessibleKeyBinding() {
        return null;
    }
}
