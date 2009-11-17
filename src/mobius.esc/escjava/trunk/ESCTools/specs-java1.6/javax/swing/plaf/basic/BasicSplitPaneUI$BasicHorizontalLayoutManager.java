package javax.swing.plaf.basic;

import javax.swing.*;
import javax.swing.event.*;
import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.util.*;

public class BasicSplitPaneUI$BasicHorizontalLayoutManager implements LayoutManager2 {
    /*synthetic*/ final BasicSplitPaneUI this$0;
    protected int[] sizes;
    protected Component[] components;
    private int lastSplitPaneSize;
    private boolean doReset;
    private int axis;
    
    BasicSplitPaneUI$BasicHorizontalLayoutManager(/*synthetic*/ final BasicSplitPaneUI this$0) {
        this(this$0, 0);
    }
    
    BasicSplitPaneUI$BasicHorizontalLayoutManager(/*synthetic*/ final BasicSplitPaneUI this$0, int axis) {
        this.this$0 = this$0;
        
        this.axis = axis;
        components = new Component[3];
        components[0] = components[1] = components[2] = null;
        sizes = new int[3];
    }
    
    public void layoutContainer(Container container) {
        Dimension containerSize = container.getSize();
        if (containerSize.height <= 0 || containerSize.width <= 0) {
            lastSplitPaneSize = 0;
            return;
        }
        int spDividerLocation = this$0.splitPane.getDividerLocation();
        Insets insets = this$0.splitPane.getInsets();
        int availableSize = getAvailableSize(containerSize, insets);
        int newSize = getSizeForPrimaryAxis(containerSize);
        int beginLocation = this$0.getDividerLocation(this$0.splitPane);
        int dOffset = getSizeForPrimaryAxis(insets, true);
        Dimension dSize = (components[2] == null) ? null : components[2].getPreferredSize();
        if ((doReset && !BasicSplitPaneUI.access$500(this$0)) || spDividerLocation < 0) {
            resetToPreferredSizes(availableSize);
        } else if (lastSplitPaneSize <= 0 || availableSize == lastSplitPaneSize || !this$0.painted || (dSize != null && getSizeForPrimaryAxis(dSize) != sizes[2])) {
            if (dSize != null) {
                sizes[2] = getSizeForPrimaryAxis(dSize);
            } else {
                sizes[2] = 0;
            }
            setDividerLocation(spDividerLocation - dOffset, availableSize);
            BasicSplitPaneUI.access$502(this$0, false);
        } else if (availableSize != lastSplitPaneSize) {
            distributeSpace(availableSize - lastSplitPaneSize, BasicSplitPaneUI.access$600(this$0));
        }
        doReset = false;
        BasicSplitPaneUI.access$502(this$0, false);
        lastSplitPaneSize = availableSize;
        int nextLocation = getInitialLocation(insets);
        int counter = 0;
        while (counter < 3) {
            if (components[counter] != null && components[counter].isVisible()) {
                setComponentToSize(components[counter], sizes[counter], nextLocation, insets, containerSize);
                nextLocation += sizes[counter];
            }
            switch (counter) {
            case 0: 
                counter = 2;
                break;
            
            case 2: 
                counter = 1;
                break;
            
            case 1: 
                counter = 3;
                break;
            
            }
        }
        if (this$0.painted) {
            int newLocation = this$0.getDividerLocation(this$0.splitPane);
            if (newLocation != (spDividerLocation - dOffset)) {
                int lastLocation = this$0.splitPane.getLastDividerLocation();
                this$0.ignoreDividerLocationChange = true;
                try {
                    this$0.splitPane.setDividerLocation(newLocation);
                    this$0.splitPane.setLastDividerLocation(lastLocation);
                } finally {
                    this$0.ignoreDividerLocationChange = false;
                }
            }
        }
    }
    
    public void addLayoutComponent(String place, Component component) {
        boolean isValid = true;
        if (place != null) {
            if (place.equals(JSplitPane.DIVIDER)) {
                components[2] = component;
                sizes[2] = getSizeForPrimaryAxis(component.getPreferredSize());
            } else if (place.equals(JSplitPane.LEFT) || place.equals(JSplitPane.TOP)) {
                components[0] = component;
                sizes[0] = 0;
            } else if (place.equals(JSplitPane.RIGHT) || place.equals(JSplitPane.BOTTOM)) {
                components[1] = component;
                sizes[1] = 0;
            } else if (!place.equals(BasicSplitPaneUI.NON_CONTINUOUS_DIVIDER)) isValid = false;
        } else {
            isValid = false;
        }
        if (!isValid) throw new IllegalArgumentException("cannot add to layout: " + "unknown constraint: " + place);
        doReset = true;
    }
    
    public Dimension minimumLayoutSize(Container container) {
        int minPrimary = 0;
        int minSecondary = 0;
        Insets insets = this$0.splitPane.getInsets();
        for (int counter = 0; counter < 3; counter++) {
            if (components[counter] != null) {
                Dimension minSize = components[counter].getMinimumSize();
                int secSize = getSizeForSecondaryAxis(minSize);
                minPrimary += getSizeForPrimaryAxis(minSize);
                if (secSize > minSecondary) minSecondary = secSize;
            }
        }
        if (insets != null) {
            minPrimary += getSizeForPrimaryAxis(insets, true) + getSizeForPrimaryAxis(insets, false);
            minSecondary += getSizeForSecondaryAxis(insets, true) + getSizeForSecondaryAxis(insets, false);
        }
        if (axis == 0) {
            return new Dimension(minPrimary, minSecondary);
        }
        return new Dimension(minSecondary, minPrimary);
    }
    
    public Dimension preferredLayoutSize(Container container) {
        int prePrimary = 0;
        int preSecondary = 0;
        Insets insets = this$0.splitPane.getInsets();
        for (int counter = 0; counter < 3; counter++) {
            if (components[counter] != null) {
                Dimension preSize = components[counter].getPreferredSize();
                int secSize = getSizeForSecondaryAxis(preSize);
                prePrimary += getSizeForPrimaryAxis(preSize);
                if (secSize > preSecondary) preSecondary = secSize;
            }
        }
        if (insets != null) {
            prePrimary += getSizeForPrimaryAxis(insets, true) + getSizeForPrimaryAxis(insets, false);
            preSecondary += getSizeForSecondaryAxis(insets, true) + getSizeForSecondaryAxis(insets, false);
        }
        if (axis == 0) {
            return new Dimension(prePrimary, preSecondary);
        }
        return new Dimension(preSecondary, prePrimary);
    }
    
    public void removeLayoutComponent(Component component) {
        for (int counter = 0; counter < 3; counter++) {
            if (components[counter] == component) {
                components[counter] = null;
                sizes[counter] = 0;
                doReset = true;
            }
        }
    }
    
    public void addLayoutComponent(Component comp, Object constraints) {
        if ((constraints == null) || (constraints instanceof String)) {
            addLayoutComponent((String)(String)constraints, comp);
        } else {
            throw new IllegalArgumentException("cannot add to layout: constraint must be a string (or null)");
        }
    }
    
    public float getLayoutAlignmentX(Container target) {
        return 0.0F;
    }
    
    public float getLayoutAlignmentY(Container target) {
        return 0.0F;
    }
    
    public void invalidateLayout(Container c) {
    }
    
    public Dimension maximumLayoutSize(Container target) {
        return new Dimension(Integer.MAX_VALUE, Integer.MAX_VALUE);
    }
    
    public void resetToPreferredSizes() {
        doReset = true;
    }
    
    protected void resetSizeAt(int index) {
        sizes[index] = 0;
        doReset = true;
    }
    
    protected void setSizes(int[] newSizes) {
        System.arraycopy(newSizes, 0, sizes, 0, 3);
    }
    
    protected int[] getSizes() {
        int[] retSizes = new int[3];
        System.arraycopy(sizes, 0, retSizes, 0, 3);
        return retSizes;
    }
    
    protected int getPreferredSizeOfComponent(Component c) {
        return getSizeForPrimaryAxis(c.getPreferredSize());
    }
    
    int getMinimumSizeOfComponent(Component c) {
        return getSizeForPrimaryAxis(c.getMinimumSize());
    }
    
    protected int getSizeOfComponent(Component c) {
        return getSizeForPrimaryAxis(c.getSize());
    }
    
    protected int getAvailableSize(Dimension containerSize, Insets insets) {
        if (insets == null) return getSizeForPrimaryAxis(containerSize);
        return (getSizeForPrimaryAxis(containerSize) - (getSizeForPrimaryAxis(insets, true) + getSizeForPrimaryAxis(insets, false)));
    }
    
    protected int getInitialLocation(Insets insets) {
        if (insets != null) return getSizeForPrimaryAxis(insets, true);
        return 0;
    }
    
    protected void setComponentToSize(Component c, int size, int location, Insets insets, Dimension containerSize) {
        if (insets != null) {
            if (axis == 0) {
                c.setBounds(location, insets.top, size, containerSize.height - (insets.top + insets.bottom));
            } else {
                c.setBounds(insets.left, location, containerSize.width - (insets.left + insets.right), size);
            }
        } else {
            if (axis == 0) {
                c.setBounds(location, 0, size, containerSize.height);
            } else {
                c.setBounds(0, location, containerSize.width, size);
            }
        }
    }
    
    int getSizeForPrimaryAxis(Dimension size) {
        if (axis == 0) {
            return size.width;
        }
        return size.height;
    }
    
    int getSizeForSecondaryAxis(Dimension size) {
        if (axis == 0) {
            return size.height;
        }
        return size.width;
    }
    
    int getSizeForPrimaryAxis(Insets insets, boolean isTop) {
        if (axis == 0) {
            if (isTop) {
                return insets.left;
            }
            return insets.right;
        }
        if (isTop) {
            return insets.top;
        }
        return insets.bottom;
    }
    
    int getSizeForSecondaryAxis(Insets insets, boolean isTop) {
        if (axis == 0) {
            if (isTop) {
                return insets.top;
            }
            return insets.bottom;
        }
        if (isTop) {
            return insets.left;
        }
        return insets.right;
    }
    
    protected void updateComponents() {
        Component comp;
        comp = this$0.splitPane.getLeftComponent();
        if (components[0] != comp) {
            components[0] = comp;
            if (comp == null) {
                sizes[0] = 0;
            } else {
                sizes[0] = -1;
            }
        }
        comp = this$0.splitPane.getRightComponent();
        if (components[1] != comp) {
            components[1] = comp;
            if (comp == null) {
                sizes[1] = 0;
            } else {
                sizes[1] = -1;
            }
        }
        Component[] children = this$0.splitPane.getComponents();
        Component oldDivider = components[2];
        components[2] = null;
        for (int counter = children.length - 1; counter >= 0; counter--) {
            if (children[counter] != components[0] && children[counter] != components[1] && children[counter] != this$0.nonContinuousLayoutDivider) {
                if (oldDivider != children[counter]) {
                    components[2] = children[counter];
                } else {
                    components[2] = oldDivider;
                }
                break;
            }
        }
        if (components[2] == null) {
            sizes[2] = 0;
        } else {
            sizes[2] = getSizeForPrimaryAxis(components[2].getPreferredSize());
        }
    }
    
    void setDividerLocation(int leftSize, int availableSize) {
        boolean lValid = (components[0] != null && components[0].isVisible());
        boolean rValid = (components[1] != null && components[1].isVisible());
        boolean dValid = (components[2] != null && components[2].isVisible());
        int max = availableSize;
        if (dValid) {
            max -= sizes[2];
        }
        leftSize = Math.max(0, Math.min(leftSize, max));
        if (lValid) {
            if (rValid) {
                sizes[0] = leftSize;
                sizes[1] = max - leftSize;
            } else {
                sizes[0] = max;
                sizes[1] = 0;
            }
        } else if (rValid) {
            sizes[1] = max;
            sizes[0] = 0;
        }
    }
    
    int[] getPreferredSizes() {
        int[] retValue = new int[3];
        for (int counter = 0; counter < 3; counter++) {
            if (components[counter] != null && components[counter].isVisible()) {
                retValue[counter] = getPreferredSizeOfComponent(components[counter]);
            } else {
                retValue[counter] = -1;
            }
        }
        return retValue;
    }
    
    int[] getMinimumSizes() {
        int[] retValue = new int[3];
        for (int counter = 0; counter < 2; counter++) {
            if (components[counter] != null && components[counter].isVisible()) {
                retValue[counter] = getMinimumSizeOfComponent(components[counter]);
            } else {
                retValue[counter] = -1;
            }
        }
        retValue[2] = (components[2] != null) ? getMinimumSizeOfComponent(components[2]) : -1;
        return retValue;
    }
    
    void resetToPreferredSizes(int availableSize) {
        int[] testSizes = getPreferredSizes();
        int totalSize = 0;
        for (int counter = 0; counter < 3; counter++) {
            if (testSizes[counter] != -1) {
                totalSize += testSizes[counter];
            }
        }
        if (totalSize > availableSize) {
            testSizes = getMinimumSizes();
            totalSize = 0;
            for (int counter = 0; counter < 3; counter++) {
                if (testSizes[counter] != -1) {
                    totalSize += testSizes[counter];
                }
            }
        }
        setSizes(testSizes);
        distributeSpace(availableSize - totalSize, false);
    }
    
    void distributeSpace(int space, boolean keepHidden) {
        boolean lValid = (components[0] != null && components[0].isVisible());
        boolean rValid = (components[1] != null && components[1].isVisible());
        if (keepHidden) {
            if (lValid && getSizeForPrimaryAxis(components[0].getSize()) == 0) {
                lValid = false;
                if (rValid && getSizeForPrimaryAxis(components[1].getSize()) == 0) {
                    lValid = true;
                }
            } else if (rValid && getSizeForPrimaryAxis(components[1].getSize()) == 0) {
                rValid = false;
            }
        }
        if (lValid && rValid) {
            double weight = this$0.splitPane.getResizeWeight();
            int lExtra = (int)(weight * (double)space);
            int rExtra = (space - lExtra);
            sizes[0] += lExtra;
            sizes[1] += rExtra;
            int lMin = getMinimumSizeOfComponent(components[0]);
            int rMin = getMinimumSizeOfComponent(components[1]);
            boolean lMinValid = (sizes[0] >= lMin);
            boolean rMinValid = (sizes[1] >= rMin);
            if (!lMinValid && !rMinValid) {
                if (sizes[0] < 0) {
                    sizes[1] += sizes[0];
                    sizes[0] = 0;
                } else if (sizes[1] < 0) {
                    sizes[0] += sizes[1];
                    sizes[1] = 0;
                }
            } else if (!lMinValid) {
                if (sizes[1] - (lMin - sizes[0]) < rMin) {
                    if (sizes[0] < 0) {
                        sizes[1] += sizes[0];
                        sizes[0] = 0;
                    }
                } else {
                    sizes[1] -= (lMin - sizes[0]);
                    sizes[0] = lMin;
                }
            } else if (!rMinValid) {
                if (sizes[0] - (rMin - sizes[1]) < lMin) {
                    if (sizes[1] < 0) {
                        sizes[0] += sizes[1];
                        sizes[1] = 0;
                    }
                } else {
                    sizes[0] -= (rMin - sizes[1]);
                    sizes[1] = rMin;
                }
            }
            if (sizes[0] < 0) {
                sizes[0] = 0;
            }
            if (sizes[1] < 0) {
                sizes[1] = 0;
            }
        } else if (lValid) {
            sizes[0] = Math.max(0, sizes[0] + space);
        } else if (rValid) {
            sizes[1] = Math.max(0, sizes[1] + space);
        }
    }
}
