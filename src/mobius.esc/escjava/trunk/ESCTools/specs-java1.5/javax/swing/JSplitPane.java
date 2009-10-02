package javax.swing;

import javax.swing.plaf.*;
import javax.accessibility.*;
import java.awt.*;
import java.io.ObjectOutputStream;
import java.io.IOException;

public class JSplitPane extends JComponent implements Accessible {
    private static final String uiClassID = "SplitPaneUI";
    public static final int VERTICAL_SPLIT = 0;
    public static final int HORIZONTAL_SPLIT = 1;
    public static final String LEFT = "left";
    public static final String RIGHT = "right";
    public static final String TOP = "top";
    public static final String BOTTOM = "bottom";
    public static final String DIVIDER = "divider";
    public static final String ORIENTATION_PROPERTY = "orientation";
    public static final String CONTINUOUS_LAYOUT_PROPERTY = "continuousLayout";
    public static final String DIVIDER_SIZE_PROPERTY = "dividerSize";
    public static final String ONE_TOUCH_EXPANDABLE_PROPERTY = "oneTouchExpandable";
    public static final String LAST_DIVIDER_LOCATION_PROPERTY = "lastDividerLocation";
    public static final String DIVIDER_LOCATION_PROPERTY = "dividerLocation";
    public static final String RESIZE_WEIGHT_PROPERTY = "resizeWeight";
    protected int orientation;
    protected boolean continuousLayout;
    protected Component leftComponent;
    protected Component rightComponent;
    protected int dividerSize;
    private boolean dividerSizeSet = false;
    protected boolean oneTouchExpandable;
    private boolean oneTouchExpandableSet;
    protected int lastDividerLocation;
    private double resizeWeight;
    private int dividerLocation;
    
    public JSplitPane() {
        this(JSplitPane.HORIZONTAL_SPLIT, false, new JButton(UIManager.getString("SplitPane.leftButtonText")), new JButton(UIManager.getString("SplitPane.rightButtonText")));
    }
    
    public JSplitPane(int newOrientation) {
        this(newOrientation, false);
    }
    
    public JSplitPane(int newOrientation, boolean newContinuousLayout) {
        this(newOrientation, newContinuousLayout, null, null);
    }
    
    public JSplitPane(int newOrientation, Component newLeftComponent, Component newRightComponent) {
        this(newOrientation, false, newLeftComponent, newRightComponent);
    }
    
    public JSplitPane(int newOrientation, boolean newContinuousLayout, Component newLeftComponent, Component newRightComponent) {
        
        dividerLocation = -1;
        setLayout(null);
        setUIProperty("opaque", Boolean.TRUE);
        orientation = newOrientation;
        if (orientation != HORIZONTAL_SPLIT && orientation != VERTICAL_SPLIT) throw new IllegalArgumentException("cannot create JSplitPane, orientation must be one of JSplitPane.HORIZONTAL_SPLIT or JSplitPane.VERTICAL_SPLIT");
        continuousLayout = newContinuousLayout;
        if (newLeftComponent != null) setLeftComponent(newLeftComponent);
        if (newRightComponent != null) setRightComponent(newRightComponent);
        updateUI();
    }
    
    public void setUI(SplitPaneUI ui) {
        if ((SplitPaneUI)(SplitPaneUI)this.ui != ui) {
            super.setUI(ui);
            revalidate();
        }
    }
    
    public SplitPaneUI getUI() {
        return (SplitPaneUI)(SplitPaneUI)ui;
    }
    
    public void updateUI() {
        setUI((SplitPaneUI)(SplitPaneUI)UIManager.getUI(this));
        revalidate();
    }
    
    public String getUIClassID() {
        return uiClassID;
    }
    
    public void setDividerSize(int newSize) {
        int oldSize = dividerSize;
        dividerSizeSet = true;
        if (oldSize != newSize) {
            dividerSize = newSize;
            firePropertyChange(DIVIDER_SIZE_PROPERTY, oldSize, newSize);
        }
    }
    
    public int getDividerSize() {
        return dividerSize;
    }
    
    public void setLeftComponent(Component comp) {
        if (comp == null) {
            if (leftComponent != null) {
                remove(leftComponent);
                leftComponent = null;
            }
        } else {
            add(comp, JSplitPane.LEFT);
        }
    }
    
    public Component getLeftComponent() {
        return leftComponent;
    }
    
    public void setTopComponent(Component comp) {
        setLeftComponent(comp);
    }
    
    public Component getTopComponent() {
        return leftComponent;
    }
    
    public void setRightComponent(Component comp) {
        if (comp == null) {
            if (rightComponent != null) {
                remove(rightComponent);
                rightComponent = null;
            }
        } else {
            add(comp, JSplitPane.RIGHT);
        }
    }
    
    public Component getRightComponent() {
        return rightComponent;
    }
    
    public void setBottomComponent(Component comp) {
        setRightComponent(comp);
    }
    
    public Component getBottomComponent() {
        return rightComponent;
    }
    
    public void setOneTouchExpandable(boolean newValue) {
        boolean oldValue = oneTouchExpandable;
        oneTouchExpandable = newValue;
        oneTouchExpandableSet = true;
        firePropertyChange(ONE_TOUCH_EXPANDABLE_PROPERTY, oldValue, newValue);
        repaint();
    }
    
    public boolean isOneTouchExpandable() {
        return oneTouchExpandable;
    }
    
    public void setLastDividerLocation(int newLastLocation) {
        int oldLocation = lastDividerLocation;
        lastDividerLocation = newLastLocation;
        firePropertyChange(LAST_DIVIDER_LOCATION_PROPERTY, oldLocation, newLastLocation);
    }
    
    public int getLastDividerLocation() {
        return lastDividerLocation;
    }
    
    public void setOrientation(int orientation) {
        if ((orientation != VERTICAL_SPLIT) && (orientation != HORIZONTAL_SPLIT)) {
            throw new IllegalArgumentException("JSplitPane: orientation must be one of JSplitPane.VERTICAL_SPLIT or JSplitPane.HORIZONTAL_SPLIT");
        }
        int oldOrientation = this.orientation;
        this.orientation = orientation;
        firePropertyChange(ORIENTATION_PROPERTY, oldOrientation, orientation);
    }
    
    public int getOrientation() {
        return orientation;
    }
    
    public void setContinuousLayout(boolean newContinuousLayout) {
        boolean oldCD = continuousLayout;
        continuousLayout = newContinuousLayout;
        firePropertyChange(CONTINUOUS_LAYOUT_PROPERTY, oldCD, newContinuousLayout);
    }
    
    public boolean isContinuousLayout() {
        return continuousLayout;
    }
    
    public void setResizeWeight(double value) {
        if (value < 0 || value > 1) {
            throw new IllegalArgumentException("JSplitPane weight must be between 0 and 1");
        }
        double oldWeight = resizeWeight;
        resizeWeight = value;
        firePropertyChange(RESIZE_WEIGHT_PROPERTY, oldWeight, value);
    }
    
    public double getResizeWeight() {
        return resizeWeight;
    }
    
    public void resetToPreferredSizes() {
        SplitPaneUI ui = getUI();
        if (ui != null) {
            ui.resetToPreferredSizes(this);
        }
    }
    
    public void setDividerLocation(double proportionalLocation) {
        if (proportionalLocation < 0.0 || proportionalLocation > 1.0) {
            throw new IllegalArgumentException("proportional location must be between 0.0 and 1.0.");
        }
        if (getOrientation() == VERTICAL_SPLIT) {
            setDividerLocation((int)((double)(getHeight() - getDividerSize()) * proportionalLocation));
        } else {
            setDividerLocation((int)((double)(getWidth() - getDividerSize()) * proportionalLocation));
        }
    }
    
    public void setDividerLocation(int location) {
        int oldValue = dividerLocation;
        dividerLocation = location;
        SplitPaneUI ui = getUI();
        if (ui != null) {
            ui.setDividerLocation(this, location);
        }
        firePropertyChange(DIVIDER_LOCATION_PROPERTY, oldValue, location);
        setLastDividerLocation(oldValue);
    }
    
    public int getDividerLocation() {
        return dividerLocation;
    }
    
    public int getMinimumDividerLocation() {
        SplitPaneUI ui = getUI();
        if (ui != null) {
            return ui.getMinimumDividerLocation(this);
        }
        return -1;
    }
    
    public int getMaximumDividerLocation() {
        SplitPaneUI ui = getUI();
        if (ui != null) {
            return ui.getMaximumDividerLocation(this);
        }
        return -1;
    }
    
    public void remove(Component component) {
        if (component == leftComponent) {
            leftComponent = null;
        } else if (component == rightComponent) {
            rightComponent = null;
        }
        super.remove(component);
        revalidate();
        repaint();
    }
    
    public void remove(int index) {
        Component comp = getComponent(index);
        if (comp == leftComponent) {
            leftComponent = null;
        } else if (comp == rightComponent) {
            rightComponent = null;
        }
        super.remove(index);
        revalidate();
        repaint();
    }
    
    public void removeAll() {
        leftComponent = rightComponent = null;
        super.removeAll();
        revalidate();
        repaint();
    }
    
    public boolean isValidateRoot() {
        return true;
    }
    
    protected void addImpl(Component comp, Object constraints, int index) {
        Component toRemove;
        if (constraints != null && !(constraints instanceof String)) {
            throw new IllegalArgumentException("cannot add to layout: constraint must be a string (or null)");
        }
        if (constraints == null) {
            if (getLeftComponent() == null) {
                constraints = JSplitPane.LEFT;
            } else if (getRightComponent() == null) {
                constraints = JSplitPane.RIGHT;
            }
        }
        if (constraints != null && (constraints.equals(JSplitPane.LEFT) || constraints.equals(JSplitPane.TOP))) {
            toRemove = getLeftComponent();
            if (toRemove != null) {
                remove(toRemove);
            }
            leftComponent = comp;
            index = -1;
        } else if (constraints != null && (constraints.equals(JSplitPane.RIGHT) || constraints.equals(JSplitPane.BOTTOM))) {
            toRemove = getRightComponent();
            if (toRemove != null) {
                remove(toRemove);
            }
            rightComponent = comp;
            index = -1;
        } else if (constraints != null && constraints.equals(JSplitPane.DIVIDER)) {
            index = -1;
        }
        super.addImpl(comp, constraints, index);
        revalidate();
        repaint();
    }
    
    protected void paintChildren(Graphics g) {
        super.paintChildren(g);
        SplitPaneUI ui = getUI();
        if (ui != null) {
            Graphics tempG = g.create();
            ui.finishedPaintingChildren(this, tempG);
            tempG.dispose();
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
    
    void setUIProperty(String propertyName, Object value) {
        if (propertyName == "dividerSize") {
            if (!dividerSizeSet) {
                setDividerSize(((Number)(Number)value).intValue());
                dividerSizeSet = false;
            }
        } else if (propertyName == "oneTouchExpandable") {
            if (!oneTouchExpandableSet) {
                setOneTouchExpandable(((Boolean)(Boolean)value).booleanValue());
                oneTouchExpandableSet = false;
            }
        } else {
            super.setUIProperty(propertyName, value);
        }
    }
    
    protected String paramString() {
        String orientationString = (orientation == HORIZONTAL_SPLIT ? "HORIZONTAL_SPLIT" : "VERTICAL_SPLIT");
        String continuousLayoutString = (continuousLayout ? "true" : "false");
        String oneTouchExpandableString = (oneTouchExpandable ? "true" : "false");
        return super.paramString() + ",continuousLayout=" + continuousLayoutString + ",dividerSize=" + dividerSize + ",lastDividerLocation=" + lastDividerLocation + ",oneTouchExpandable=" + oneTouchExpandableString + ",orientation=" + orientationString;
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JSplitPane$AccessibleJSplitPane(this);
        }
        return accessibleContext;
    }
    {
    }
}
