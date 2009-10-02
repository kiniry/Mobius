package javax.swing;

import java.awt.Component;
import java.awt.Adjustable;
import java.awt.Dimension;
import java.awt.event.AdjustmentListener;
import java.awt.event.AdjustmentEvent;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;
import java.io.ObjectOutputStream;
import java.io.IOException;

public class JScrollBar extends JComponent implements Adjustable, Accessible {
    
    /*synthetic*/ static void access$100(JScrollBar x0, int x1, int x2, int x3, boolean x4) {
        x0.fireAdjustmentValueChanged(x1, x2, x3, x4);
    }
    {
    }
    private static final String uiClassID = "ScrollBarUI";
    private ChangeListener fwdAdjustmentEvents = new JScrollBar$ModelListener(this, null);
    protected BoundedRangeModel model;
    protected int orientation;
    protected int unitIncrement;
    protected int blockIncrement;
    
    private void checkOrientation(int orientation) {
        switch (orientation) {
        case VERTICAL: 
        
        case HORIZONTAL: 
            break;
        
        default: 
            throw new IllegalArgumentException("orientation must be one of: VERTICAL, HORIZONTAL");
        
        }
    }
    
    public JScrollBar(int orientation, int value, int extent, int min, int max) {
        
        checkOrientation(orientation);
        this.unitIncrement = 1;
        this.blockIncrement = (extent == 0) ? 1 : extent;
        this.orientation = orientation;
        this.model = new DefaultBoundedRangeModel(value, extent, min, max);
        this.model.addChangeListener(fwdAdjustmentEvents);
        setRequestFocusEnabled(false);
        updateUI();
    }
    
    public JScrollBar(int orientation) {
        this(orientation, 0, 10, 0, 100);
    }
    
    public JScrollBar() {
        this(VERTICAL);
    }
    
    public void setUI(ScrollBarUI ui) {
        super.setUI(ui);
    }
    
    public ScrollBarUI getUI() {
        return (ScrollBarUI)(ScrollBarUI)ui;
    }
    
    public void updateUI() {
        setUI((ScrollBarUI)(ScrollBarUI)UIManager.getUI(this));
    }
    
    public String getUIClassID() {
        return uiClassID;
    }
    
    public int getOrientation() {
        return orientation;
    }
    
    public void setOrientation(int orientation) {
        checkOrientation(orientation);
        int oldValue = this.orientation;
        this.orientation = orientation;
        firePropertyChange("orientation", oldValue, orientation);
        if ((oldValue != orientation) && (accessibleContext != null)) {
            accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, ((oldValue == VERTICAL) ? AccessibleState.VERTICAL : AccessibleState.HORIZONTAL), ((orientation == VERTICAL) ? AccessibleState.VERTICAL : AccessibleState.HORIZONTAL));
        }
        if (orientation != oldValue) {
            revalidate();
        }
    }
    
    public BoundedRangeModel getModel() {
        return model;
    }
    
    public void setModel(BoundedRangeModel newModel) {
        Integer oldValue = null;
        BoundedRangeModel oldModel = model;
        if (model != null) {
            model.removeChangeListener(fwdAdjustmentEvents);
            oldValue = new Integer(model.getValue());
        }
        model = newModel;
        if (model != null) {
            model.addChangeListener(fwdAdjustmentEvents);
        }
        firePropertyChange("model", oldModel, model);
        if (accessibleContext != null) {
            accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_VALUE_PROPERTY, oldValue, new Integer(model.getValue()));
        }
    }
    
    public int getUnitIncrement(int direction) {
        return unitIncrement;
    }
    
    public void setUnitIncrement(int unitIncrement) {
        int oldValue = this.unitIncrement;
        this.unitIncrement = unitIncrement;
        firePropertyChange("unitIncrement", oldValue, unitIncrement);
    }
    
    public int getBlockIncrement(int direction) {
        return blockIncrement;
    }
    
    public void setBlockIncrement(int blockIncrement) {
        int oldValue = this.blockIncrement;
        this.blockIncrement = blockIncrement;
        firePropertyChange("blockIncrement", oldValue, blockIncrement);
    }
    
    public int getUnitIncrement() {
        return unitIncrement;
    }
    
    public int getBlockIncrement() {
        return blockIncrement;
    }
    
    public int getValue() {
        return getModel().getValue();
    }
    
    public void setValue(int value) {
        BoundedRangeModel m = getModel();
        int oldValue = m.getValue();
        m.setValue(value);
        if (accessibleContext != null) {
            accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_VALUE_PROPERTY, new Integer(oldValue), new Integer(m.getValue()));
        }
    }
    
    public int getVisibleAmount() {
        return getModel().getExtent();
    }
    
    public void setVisibleAmount(int extent) {
        getModel().setExtent(extent);
    }
    
    public int getMinimum() {
        return getModel().getMinimum();
    }
    
    public void setMinimum(int minimum) {
        getModel().setMinimum(minimum);
    }
    
    public int getMaximum() {
        return getModel().getMaximum();
    }
    
    public void setMaximum(int maximum) {
        getModel().setMaximum(maximum);
    }
    
    public boolean getValueIsAdjusting() {
        return getModel().getValueIsAdjusting();
    }
    
    public void setValueIsAdjusting(boolean b) {
        BoundedRangeModel m = getModel();
        boolean oldValue = m.getValueIsAdjusting();
        m.setValueIsAdjusting(b);
        if ((oldValue != b) && (accessibleContext != null)) {
            accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_STATE_PROPERTY, ((oldValue) ? AccessibleState.BUSY : null), ((b) ? AccessibleState.BUSY : null));
        }
    }
    
    public void setValues(int newValue, int newExtent, int newMin, int newMax) {
        BoundedRangeModel m = getModel();
        int oldValue = m.getValue();
        m.setRangeProperties(newValue, newExtent, newMin, newMax, m.getValueIsAdjusting());
        if (accessibleContext != null) {
            accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_VALUE_PROPERTY, new Integer(oldValue), new Integer(m.getValue()));
        }
    }
    
    public void addAdjustmentListener(AdjustmentListener l) {
        listenerList.add(AdjustmentListener.class, l);
    }
    
    public void removeAdjustmentListener(AdjustmentListener l) {
        listenerList.remove(AdjustmentListener.class, l);
    }
    
    public AdjustmentListener[] getAdjustmentListeners() {
        return (AdjustmentListener[])(AdjustmentListener[])listenerList.getListeners(AdjustmentListener.class);
    }
    
    protected void fireAdjustmentValueChanged(int id, int type, int value) {
        fireAdjustmentValueChanged(id, type, value, getValueIsAdjusting());
    }
    
    private void fireAdjustmentValueChanged(int id, int type, int value, boolean isAdjusting) {
        Object[] listeners = listenerList.getListenerList();
        AdjustmentEvent e = null;
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == AdjustmentListener.class) {
                if (e == null) {
                    e = new AdjustmentEvent(this, id, type, value, isAdjusting);
                }
                ((AdjustmentListener)(AdjustmentListener)listeners[i + 1]).adjustmentValueChanged(e);
            }
        }
    }
    {
    }
    
    public Dimension getMinimumSize() {
        Dimension pref = getPreferredSize();
        if (orientation == VERTICAL) {
            return new Dimension(pref.width, 5);
        } else {
            return new Dimension(5, pref.height);
        }
    }
    
    public Dimension getMaximumSize() {
        Dimension pref = getPreferredSize();
        if (getOrientation() == VERTICAL) {
            return new Dimension(pref.width, Short.MAX_VALUE);
        } else {
            return new Dimension(Short.MAX_VALUE, pref.height);
        }
    }
    
    public void setEnabled(boolean x) {
        super.setEnabled(x);
        Component[] children = getComponents();
        for (int i = 0; i < children.length; i++) {
            children[i].setEnabled(x);
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
    
    protected String paramString() {
        String orientationString = (orientation == HORIZONTAL ? "HORIZONTAL" : "VERTICAL");
        return super.paramString() + ",blockIncrement=" + blockIncrement + ",orientation=" + orientationString + ",unitIncrement=" + unitIncrement;
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JScrollBar$AccessibleJScrollBar(this);
        }
        return accessibleContext;
    }
    {
    }
}
