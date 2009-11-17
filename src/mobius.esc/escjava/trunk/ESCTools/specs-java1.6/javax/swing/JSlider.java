package javax.swing;

import javax.swing.border.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;
import java.io.ObjectOutputStream;
import java.io.IOException;
import java.util.*;
import java.beans.*;

public class JSlider extends JComponent implements SwingConstants, Accessible {
    {
    }
    private static final String uiClassID = "SliderUI";
    private boolean paintTicks = false;
    private boolean paintTrack = true;
    private boolean paintLabels = false;
    private boolean isInverted = false;
    protected BoundedRangeModel sliderModel;
    protected int majorTickSpacing;
    protected int minorTickSpacing;
    protected boolean snapToTicks = false;
    boolean snapToValue = true;
    protected int orientation;
    private Dictionary labelTable;
    protected ChangeListener changeListener = createChangeListener();
    protected transient ChangeEvent changeEvent = null;
    
    private void checkOrientation(int orientation) {
        switch (orientation) {
        case VERTICAL: 
        
        case HORIZONTAL: 
            break;
        
        default: 
            throw new IllegalArgumentException("orientation must be one of: VERTICAL, HORIZONTAL");
        
        }
    }
    
    public JSlider() {
        this(HORIZONTAL, 0, 100, 50);
    }
    
    public JSlider(int orientation) {
        this(orientation, 0, 100, 50);
    }
    
    public JSlider(int min, int max) {
        this(HORIZONTAL, min, max, (min + max) / 2);
    }
    
    public JSlider(int min, int max, int value) {
        this(HORIZONTAL, min, max, value);
    }
    
    public JSlider(int orientation, int min, int max, int value) {
        
        checkOrientation(orientation);
        this.orientation = orientation;
        sliderModel = new DefaultBoundedRangeModel(value, 0, min, max);
        sliderModel.addChangeListener(changeListener);
        updateUI();
    }
    
    public JSlider(BoundedRangeModel brm) {
        
        this.orientation = JSlider.HORIZONTAL;
        setModel(brm);
        sliderModel.addChangeListener(changeListener);
        updateUI();
    }
    
    public SliderUI getUI() {
        return (SliderUI)(SliderUI)ui;
    }
    
    public void setUI(SliderUI ui) {
        super.setUI(ui);
    }
    
    public void updateUI() {
        updateLabelUIs();
        setUI((SliderUI)(SliderUI)UIManager.getUI(this));
    }
    
    public String getUIClassID() {
        return uiClassID;
    }
    {
    }
    
    protected ChangeListener createChangeListener() {
        return new JSlider$ModelListener(this, null);
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
                if (changeEvent == null) {
                    changeEvent = new ChangeEvent(this);
                }
                ((ChangeListener)(ChangeListener)listeners[i + 1]).stateChanged(changeEvent);
            }
        }
    }
    
    public BoundedRangeModel getModel() {
        return sliderModel;
    }
    
    public void setModel(BoundedRangeModel newModel) {
        BoundedRangeModel oldModel = getModel();
        if (oldModel != null) {
            oldModel.removeChangeListener(changeListener);
        }
        sliderModel = newModel;
        if (newModel != null) {
            newModel.addChangeListener(changeListener);
            if (accessibleContext != null) {
                accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_VALUE_PROPERTY, (oldModel == null ? null : new Integer(oldModel.getValue())), (newModel == null ? null : new Integer(newModel.getValue())));
            }
        }
        firePropertyChange("model", oldModel, sliderModel);
    }
    
    public int getValue() {
        return getModel().getValue();
    }
    
    public void setValue(int n) {
        BoundedRangeModel m = getModel();
        int oldValue = m.getValue();
        if (oldValue == n) {
            return;
        }
        m.setValue(n);
        if (accessibleContext != null) {
            accessibleContext.firePropertyChange(AccessibleContext.ACCESSIBLE_VALUE_PROPERTY, new Integer(oldValue), new Integer(m.getValue()));
        }
    }
    
    public int getMinimum() {
        return getModel().getMinimum();
    }
    
    public void setMinimum(int minimum) {
        int oldMin = getModel().getMinimum();
        getModel().setMinimum(minimum);
        firePropertyChange("minimum", new Integer(oldMin), new Integer(minimum));
    }
    
    public int getMaximum() {
        return getModel().getMaximum();
    }
    
    public void setMaximum(int maximum) {
        int oldMax = getModel().getMaximum();
        getModel().setMaximum(maximum);
        firePropertyChange("maximum", new Integer(oldMax), new Integer(maximum));
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
    
    public int getExtent() {
        return getModel().getExtent();
    }
    
    public void setExtent(int extent) {
        getModel().setExtent(extent);
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
    
    public Dictionary getLabelTable() {
        return labelTable;
    }
    
    public void setLabelTable(Dictionary labels) {
        Dictionary oldTable = labelTable;
        labelTable = labels;
        updateLabelUIs();
        firePropertyChange("labelTable", oldTable, labelTable);
        if (labels != oldTable) {
            revalidate();
            repaint();
        }
    }
    
    protected void updateLabelUIs() {
        if (getLabelTable() == null) {
            return;
        }
        Enumeration labels = getLabelTable().keys();
        while (labels.hasMoreElements()) {
            Object value = getLabelTable().get(labels.nextElement());
            if (value instanceof JComponent) {
                JComponent component = (JComponent)(JComponent)value;
                component.updateUI();
                component.setSize(component.getPreferredSize());
            }
        }
    }
    
    public Hashtable createStandardLabels(int increment) {
        return createStandardLabels(increment, getMinimum());
    }
    
    public Hashtable createStandardLabels(int increment, int start) {
        if (start > getMaximum() || start < getMinimum()) {
            throw new IllegalArgumentException("Slider label start point out of range.");
        }
        if (increment <= 0) {
            throw new IllegalArgumentException("Label incremement must be > 0");
        }
        {
        }
        JSlider$1SmartHashtable table = new JSlider$1SmartHashtable(this, increment, start);
        if (getLabelTable() != null && (getLabelTable() instanceof PropertyChangeListener)) {
            removePropertyChangeListener((PropertyChangeListener)(PropertyChangeListener)getLabelTable());
        }
        addPropertyChangeListener(table);
        return table;
    }
    
    public boolean getInverted() {
        return isInverted;
    }
    
    public void setInverted(boolean b) {
        boolean oldValue = isInverted;
        isInverted = b;
        firePropertyChange("inverted", oldValue, isInverted);
        if (b != oldValue) {
            repaint();
        }
    }
    
    public int getMajorTickSpacing() {
        return majorTickSpacing;
    }
    
    public void setMajorTickSpacing(int n) {
        int oldValue = majorTickSpacing;
        majorTickSpacing = n;
        if (labelTable == null && getMajorTickSpacing() > 0 && getPaintLabels()) {
            setLabelTable(createStandardLabels(getMajorTickSpacing()));
        }
        firePropertyChange("majorTickSpacing", oldValue, majorTickSpacing);
        if (majorTickSpacing != oldValue && getPaintTicks()) {
            repaint();
        }
    }
    
    public int getMinorTickSpacing() {
        return minorTickSpacing;
    }
    
    public void setMinorTickSpacing(int n) {
        int oldValue = minorTickSpacing;
        minorTickSpacing = n;
        firePropertyChange("minorTickSpacing", oldValue, minorTickSpacing);
        if (minorTickSpacing != oldValue && getPaintTicks()) {
            repaint();
        }
    }
    
    public boolean getSnapToTicks() {
        return snapToTicks;
    }
    
    boolean getSnapToValue() {
        return snapToValue;
    }
    
    public void setSnapToTicks(boolean b) {
        boolean oldValue = snapToTicks;
        snapToTicks = b;
        firePropertyChange("snapToTicks", oldValue, snapToTicks);
    }
    
    void setSnapToValue(boolean b) {
        boolean oldValue = snapToValue;
        snapToValue = b;
        firePropertyChange("snapToValue", oldValue, snapToValue);
    }
    
    public boolean getPaintTicks() {
        return paintTicks;
    }
    
    public void setPaintTicks(boolean b) {
        boolean oldValue = paintTicks;
        paintTicks = b;
        firePropertyChange("paintTicks", oldValue, paintTicks);
        if (paintTicks != oldValue) {
            revalidate();
            repaint();
        }
    }
    
    public boolean getPaintTrack() {
        return paintTrack;
    }
    
    public void setPaintTrack(boolean b) {
        boolean oldValue = paintTrack;
        paintTrack = b;
        firePropertyChange("paintTrack", oldValue, paintTrack);
        if (paintTrack != oldValue) {
            repaint();
        }
    }
    
    public boolean getPaintLabels() {
        return paintLabels;
    }
    
    public void setPaintLabels(boolean b) {
        boolean oldValue = paintLabels;
        paintLabels = b;
        if (labelTable == null && getMajorTickSpacing() > 0) {
            setLabelTable(createStandardLabels(getMajorTickSpacing()));
        }
        firePropertyChange("paintLabels", oldValue, paintLabels);
        if (paintLabels != oldValue) {
            revalidate();
            repaint();
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
        String paintTicksString = (paintTicks ? "true" : "false");
        String paintTrackString = (paintTrack ? "true" : "false");
        String paintLabelsString = (paintLabels ? "true" : "false");
        String isInvertedString = (isInverted ? "true" : "false");
        String snapToTicksString = (snapToTicks ? "true" : "false");
        String snapToValueString = (snapToValue ? "true" : "false");
        String orientationString = (orientation == HORIZONTAL ? "HORIZONTAL" : "VERTICAL");
        return super.paramString() + ",isInverted=" + isInvertedString + ",majorTickSpacing=" + majorTickSpacing + ",minorTickSpacing=" + minorTickSpacing + ",orientation=" + orientationString + ",paintLabels=" + paintLabelsString + ",paintTicks=" + paintTicksString + ",paintTrack=" + paintTrackString + ",snapToTicks=" + snapToTicksString + ",snapToValue=" + snapToValueString;
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JSlider$AccessibleJSlider(this);
        }
        return accessibleContext;
    }
    {
    }
}
