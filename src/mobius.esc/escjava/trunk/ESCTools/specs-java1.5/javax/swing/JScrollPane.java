package javax.swing;

import javax.swing.plaf.*;
import javax.swing.border.*;
import javax.swing.event.*;
import javax.accessibility.*;
import java.awt.Component;
import java.awt.ComponentOrientation;
import java.awt.Rectangle;
import java.awt.Insets;
import java.awt.LayoutManager;
import java.awt.Point;
import java.io.ObjectOutputStream;
import java.io.IOException;
import java.beans.*;

public class JScrollPane extends JComponent implements ScrollPaneConstants, Accessible {
    private Border viewportBorder;
    private static final String uiClassID = "ScrollPaneUI";
    protected int verticalScrollBarPolicy = VERTICAL_SCROLLBAR_AS_NEEDED;
    protected int horizontalScrollBarPolicy = HORIZONTAL_SCROLLBAR_AS_NEEDED;
    protected JViewport viewport;
    protected JScrollBar verticalScrollBar;
    protected JScrollBar horizontalScrollBar;
    protected JViewport rowHeader;
    protected JViewport columnHeader;
    protected Component lowerLeft;
    protected Component lowerRight;
    protected Component upperLeft;
    protected Component upperRight;
    private boolean wheelScrollState = true;
    
    public JScrollPane(Component view, int vsbPolicy, int hsbPolicy) {
        
        setLayout(new ScrollPaneLayout$UIResource());
        setVerticalScrollBarPolicy(vsbPolicy);
        setHorizontalScrollBarPolicy(hsbPolicy);
        setViewport(createViewport());
        setVerticalScrollBar(createVerticalScrollBar());
        setHorizontalScrollBar(createHorizontalScrollBar());
        if (view != null) {
            setViewportView(view);
        }
        setOpaque(true);
        updateUI();
        if (!this.getComponentOrientation().isLeftToRight()) {
            viewport.setViewPosition(new Point(Integer.MAX_VALUE, 0));
        }
    }
    
    public JScrollPane(Component view) {
        this(view, VERTICAL_SCROLLBAR_AS_NEEDED, HORIZONTAL_SCROLLBAR_AS_NEEDED);
    }
    
    public JScrollPane(int vsbPolicy, int hsbPolicy) {
        this(null, vsbPolicy, hsbPolicy);
    }
    
    public JScrollPane() {
        this(null, VERTICAL_SCROLLBAR_AS_NEEDED, HORIZONTAL_SCROLLBAR_AS_NEEDED);
    }
    
    public ScrollPaneUI getUI() {
        return (ScrollPaneUI)(ScrollPaneUI)ui;
    }
    
    public void setUI(ScrollPaneUI ui) {
        super.setUI(ui);
    }
    
    public void updateUI() {
        setUI((ScrollPaneUI)(ScrollPaneUI)UIManager.getUI(this));
    }
    
    public String getUIClassID() {
        return uiClassID;
    }
    
    public void setLayout(LayoutManager layout) {
        if (layout instanceof ScrollPaneLayout) {
            super.setLayout(layout);
            ((ScrollPaneLayout)(ScrollPaneLayout)layout).syncWithScrollPane(this);
        } else if (layout == null) {
            super.setLayout(layout);
        } else {
            String s = "layout of JScrollPane must be a ScrollPaneLayout";
            throw new ClassCastException(s);
        }
    }
    
    public boolean isValidateRoot() {
        return true;
    }
    
    public int getVerticalScrollBarPolicy() {
        return verticalScrollBarPolicy;
    }
    
    public void setVerticalScrollBarPolicy(int policy) {
        switch (policy) {
        case VERTICAL_SCROLLBAR_AS_NEEDED: 
        
        case VERTICAL_SCROLLBAR_NEVER: 
        
        case VERTICAL_SCROLLBAR_ALWAYS: 
            break;
        
        default: 
            throw new IllegalArgumentException("invalid verticalScrollBarPolicy");
        
        }
        int old = verticalScrollBarPolicy;
        verticalScrollBarPolicy = policy;
        firePropertyChange("verticalScrollBarPolicy", old, policy);
        revalidate();
        repaint();
    }
    
    public int getHorizontalScrollBarPolicy() {
        return horizontalScrollBarPolicy;
    }
    
    public void setHorizontalScrollBarPolicy(int policy) {
        switch (policy) {
        case HORIZONTAL_SCROLLBAR_AS_NEEDED: 
        
        case HORIZONTAL_SCROLLBAR_NEVER: 
        
        case HORIZONTAL_SCROLLBAR_ALWAYS: 
            break;
        
        default: 
            throw new IllegalArgumentException("invalid horizontalScrollBarPolicy");
        
        }
        int old = horizontalScrollBarPolicy;
        horizontalScrollBarPolicy = policy;
        firePropertyChange("horizontalScrollBarPolicy", old, policy);
        revalidate();
        repaint();
    }
    
    public Border getViewportBorder() {
        return viewportBorder;
    }
    
    public void setViewportBorder(Border viewportBorder) {
        Border oldValue = this.viewportBorder;
        this.viewportBorder = viewportBorder;
        firePropertyChange("viewportBorder", oldValue, viewportBorder);
    }
    
    public Rectangle getViewportBorderBounds() {
        Rectangle borderR = new Rectangle(getSize());
        Insets insets = getInsets();
        borderR.x = insets.left;
        borderR.y = insets.top;
        borderR.width -= insets.left + insets.right;
        borderR.height -= insets.top + insets.bottom;
        boolean leftToRight = SwingUtilities.isLeftToRight(this);
        JViewport colHead = getColumnHeader();
        if ((colHead != null) && (colHead.isVisible())) {
            int colHeadHeight = colHead.getHeight();
            borderR.y += colHeadHeight;
            borderR.height -= colHeadHeight;
        }
        JViewport rowHead = getRowHeader();
        if ((rowHead != null) && (rowHead.isVisible())) {
            int rowHeadWidth = rowHead.getWidth();
            if (leftToRight) {
                borderR.x += rowHeadWidth;
            }
            borderR.width -= rowHeadWidth;
        }
        JScrollBar vsb = getVerticalScrollBar();
        if ((vsb != null) && (vsb.isVisible())) {
            int vsbWidth = vsb.getWidth();
            if (!leftToRight) {
                borderR.x += vsbWidth;
            }
            borderR.width -= vsbWidth;
        }
        JScrollBar hsb = getHorizontalScrollBar();
        if ((hsb != null) && (hsb.isVisible())) {
            borderR.height -= hsb.getHeight();
        }
        return borderR;
    }
    {
    }
    
    public JScrollBar createHorizontalScrollBar() {
        return new JScrollPane$ScrollBar(this, JScrollBar.HORIZONTAL);
    }
    
    public JScrollBar getHorizontalScrollBar() {
        return horizontalScrollBar;
    }
    
    public void setHorizontalScrollBar(JScrollBar horizontalScrollBar) {
        JScrollBar old = getHorizontalScrollBar();
        this.horizontalScrollBar = horizontalScrollBar;
        if (horizontalScrollBar != null) {
            add(horizontalScrollBar, HORIZONTAL_SCROLLBAR);
        } else if (old != null) {
            remove(old);
        }
        firePropertyChange("horizontalScrollBar", old, horizontalScrollBar);
        revalidate();
        repaint();
    }
    
    public JScrollBar createVerticalScrollBar() {
        return new JScrollPane$ScrollBar(this, JScrollBar.VERTICAL);
    }
    
    public JScrollBar getVerticalScrollBar() {
        return verticalScrollBar;
    }
    
    public void setVerticalScrollBar(JScrollBar verticalScrollBar) {
        JScrollBar old = getVerticalScrollBar();
        this.verticalScrollBar = verticalScrollBar;
        add(verticalScrollBar, VERTICAL_SCROLLBAR);
        firePropertyChange("verticalScrollBar", old, verticalScrollBar);
        revalidate();
        repaint();
    }
    
    protected JViewport createViewport() {
        return new JViewport();
    }
    
    public JViewport getViewport() {
        return viewport;
    }
    
    public void setViewport(JViewport viewport) {
        JViewport old = getViewport();
        this.viewport = viewport;
        if (viewport != null) {
            add(viewport, VIEWPORT);
        } else if (old != null) {
            remove(old);
        }
        firePropertyChange("viewport", old, viewport);
        if (accessibleContext != null) {
            ((JScrollPane$AccessibleJScrollPane)(JScrollPane$AccessibleJScrollPane)accessibleContext).resetViewPort();
        }
        revalidate();
        repaint();
    }
    
    public void setViewportView(Component view) {
        if (getViewport() == null) {
            setViewport(createViewport());
        }
        getViewport().setView(view);
    }
    
    public JViewport getRowHeader() {
        return rowHeader;
    }
    
    public void setRowHeader(JViewport rowHeader) {
        JViewport old = getRowHeader();
        this.rowHeader = rowHeader;
        if (rowHeader != null) {
            add(rowHeader, ROW_HEADER);
        } else if (old != null) {
            remove(old);
        }
        firePropertyChange("rowHeader", old, rowHeader);
        revalidate();
        repaint();
    }
    
    public void setRowHeaderView(Component view) {
        if (getRowHeader() == null) {
            setRowHeader(createViewport());
        }
        getRowHeader().setView(view);
    }
    
    public JViewport getColumnHeader() {
        return columnHeader;
    }
    
    public void setColumnHeader(JViewport columnHeader) {
        JViewport old = getColumnHeader();
        this.columnHeader = columnHeader;
        if (columnHeader != null) {
            add(columnHeader, COLUMN_HEADER);
        } else if (old != null) {
            remove(old);
        }
        firePropertyChange("columnHeader", old, columnHeader);
        revalidate();
        repaint();
    }
    
    public void setColumnHeaderView(Component view) {
        if (getColumnHeader() == null) {
            setColumnHeader(createViewport());
        }
        getColumnHeader().setView(view);
    }
    
    public Component getCorner(String key) {
        boolean isLeftToRight = getComponentOrientation().isLeftToRight();
        if (key.equals(LOWER_LEADING_CORNER)) {
            key = isLeftToRight ? LOWER_LEFT_CORNER : LOWER_RIGHT_CORNER;
        } else if (key.equals(LOWER_TRAILING_CORNER)) {
            key = isLeftToRight ? LOWER_RIGHT_CORNER : LOWER_LEFT_CORNER;
        } else if (key.equals(UPPER_LEADING_CORNER)) {
            key = isLeftToRight ? UPPER_LEFT_CORNER : UPPER_RIGHT_CORNER;
        } else if (key.equals(UPPER_TRAILING_CORNER)) {
            key = isLeftToRight ? UPPER_RIGHT_CORNER : UPPER_LEFT_CORNER;
        }
        if (key.equals(LOWER_LEFT_CORNER)) {
            return lowerLeft;
        } else if (key.equals(LOWER_RIGHT_CORNER)) {
            return lowerRight;
        } else if (key.equals(UPPER_LEFT_CORNER)) {
            return upperLeft;
        } else if (key.equals(UPPER_RIGHT_CORNER)) {
            return upperRight;
        } else {
            return null;
        }
    }
    
    public void setCorner(String key, Component corner) {
        Component old;
        boolean isLeftToRight = getComponentOrientation().isLeftToRight();
        if (key.equals(LOWER_LEADING_CORNER)) {
            key = isLeftToRight ? LOWER_LEFT_CORNER : LOWER_RIGHT_CORNER;
        } else if (key.equals(LOWER_TRAILING_CORNER)) {
            key = isLeftToRight ? LOWER_RIGHT_CORNER : LOWER_LEFT_CORNER;
        } else if (key.equals(UPPER_LEADING_CORNER)) {
            key = isLeftToRight ? UPPER_LEFT_CORNER : UPPER_RIGHT_CORNER;
        } else if (key.equals(UPPER_TRAILING_CORNER)) {
            key = isLeftToRight ? UPPER_RIGHT_CORNER : UPPER_LEFT_CORNER;
        }
        if (key.equals(LOWER_LEFT_CORNER)) {
            old = lowerLeft;
            lowerLeft = corner;
        } else if (key.equals(LOWER_RIGHT_CORNER)) {
            old = lowerRight;
            lowerRight = corner;
        } else if (key.equals(UPPER_LEFT_CORNER)) {
            old = upperLeft;
            upperLeft = corner;
        } else if (key.equals(UPPER_RIGHT_CORNER)) {
            old = upperRight;
            upperRight = corner;
        } else {
            throw new IllegalArgumentException("invalid corner key");
        }
        if (old != null) {
            remove(old);
        }
        if (corner != null) {
            add(corner, key);
        }
        firePropertyChange(key, old, corner);
        revalidate();
        repaint();
    }
    
    public void setComponentOrientation(ComponentOrientation co) {
        super.setComponentOrientation(co);
        if (verticalScrollBar != null) verticalScrollBar.setComponentOrientation(co);
        if (horizontalScrollBar != null) horizontalScrollBar.setComponentOrientation(co);
    }
    
    public boolean isWheelScrollingEnabled() {
        return wheelScrollState;
    }
    
    public void setWheelScrollingEnabled(boolean handleWheel) {
        boolean old = wheelScrollState;
        wheelScrollState = handleWheel;
        firePropertyChange("wheelScrollingEnabled", old, handleWheel);
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
        String viewportBorderString = (viewportBorder != null ? viewportBorder.toString() : "");
        String viewportString = (viewport != null ? viewport.toString() : "");
        String verticalScrollBarPolicyString;
        if (verticalScrollBarPolicy == VERTICAL_SCROLLBAR_AS_NEEDED) {
            verticalScrollBarPolicyString = "VERTICAL_SCROLLBAR_AS_NEEDED";
        } else if (verticalScrollBarPolicy == VERTICAL_SCROLLBAR_NEVER) {
            verticalScrollBarPolicyString = "VERTICAL_SCROLLBAR_NEVER";
        } else if (verticalScrollBarPolicy == VERTICAL_SCROLLBAR_ALWAYS) {
            verticalScrollBarPolicyString = "VERTICAL_SCROLLBAR_ALWAYS";
        } else verticalScrollBarPolicyString = "";
        String horizontalScrollBarPolicyString;
        if (horizontalScrollBarPolicy == HORIZONTAL_SCROLLBAR_AS_NEEDED) {
            horizontalScrollBarPolicyString = "HORIZONTAL_SCROLLBAR_AS_NEEDED";
        } else if (horizontalScrollBarPolicy == HORIZONTAL_SCROLLBAR_NEVER) {
            horizontalScrollBarPolicyString = "HORIZONTAL_SCROLLBAR_NEVER";
        } else if (horizontalScrollBarPolicy == HORIZONTAL_SCROLLBAR_ALWAYS) {
            horizontalScrollBarPolicyString = "HORIZONTAL_SCROLLBAR_ALWAYS";
        } else horizontalScrollBarPolicyString = "";
        String horizontalScrollBarString = (horizontalScrollBar != null ? horizontalScrollBar.toString() : "");
        String verticalScrollBarString = (verticalScrollBar != null ? verticalScrollBar.toString() : "");
        String columnHeaderString = (columnHeader != null ? columnHeader.toString() : "");
        String rowHeaderString = (rowHeader != null ? rowHeader.toString() : "");
        String lowerLeftString = (lowerLeft != null ? lowerLeft.toString() : "");
        String lowerRightString = (lowerRight != null ? lowerRight.toString() : "");
        String upperLeftString = (upperLeft != null ? upperLeft.toString() : "");
        String upperRightString = (upperRight != null ? upperRight.toString() : "");
        return super.paramString() + ",columnHeader=" + columnHeaderString + ",horizontalScrollBar=" + horizontalScrollBarString + ",horizontalScrollBarPolicy=" + horizontalScrollBarPolicyString + ",lowerLeft=" + lowerLeftString + ",lowerRight=" + lowerRightString + ",rowHeader=" + rowHeaderString + ",upperLeft=" + upperLeftString + ",upperRight=" + upperRightString + ",verticalScrollBar=" + verticalScrollBarString + ",verticalScrollBarPolicy=" + verticalScrollBarPolicyString + ",viewport=" + viewportString + ",viewportBorder=" + viewportBorderString;
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JScrollPane$AccessibleJScrollPane(this);
        }
        return accessibleContext;
    }
    {
    }
}
