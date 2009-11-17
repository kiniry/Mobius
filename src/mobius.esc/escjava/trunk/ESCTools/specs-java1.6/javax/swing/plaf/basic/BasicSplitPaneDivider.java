package javax.swing.plaf.basic;

import java.awt.*;
import java.awt.event.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.swing.border.Border;
import java.beans.*;
import sun.swing.DefaultLookup;

public class BasicSplitPaneDivider extends Container implements PropertyChangeListener {
    
    /*synthetic*/ static int access$200(BasicSplitPaneDivider x0) {
        return x0.oneTouchOffset;
    }
    
    /*synthetic*/ static boolean access$100(BasicSplitPaneDivider x0) {
        return x0.centerOneTouchButtons;
    }
    
    /*synthetic*/ static int access$000(BasicSplitPaneDivider x0) {
        return x0.oneTouchSize;
    }
    protected static final int ONE_TOUCH_SIZE = 6;
    protected static final int ONE_TOUCH_OFFSET = 2;
    protected BasicSplitPaneDivider$DragController dragger;
    protected BasicSplitPaneUI splitPaneUI;
    protected int dividerSize = 0;
    protected Component hiddenDivider;
    protected JSplitPane splitPane;
    protected BasicSplitPaneDivider$MouseHandler mouseHandler;
    protected int orientation;
    protected JButton leftButton;
    protected JButton rightButton;
    private Border border;
    private boolean mouseOver;
    private int oneTouchSize;
    private int oneTouchOffset;
    private boolean centerOneTouchButtons;
    
    public BasicSplitPaneDivider(BasicSplitPaneUI ui) {
        
        oneTouchSize = DefaultLookup.getInt(ui.getSplitPane(), ui, "SplitPane.oneTouchButtonSize", ONE_TOUCH_SIZE);
        oneTouchOffset = DefaultLookup.getInt(ui.getSplitPane(), ui, "SplitPane.oneTouchButtonOffset", ONE_TOUCH_OFFSET);
        centerOneTouchButtons = DefaultLookup.getBoolean(ui.getSplitPane(), ui, "SplitPane.centerOneTouchButtons", true);
        setLayout(new BasicSplitPaneDivider$DividerLayout(this));
        setBasicSplitPaneUI(ui);
        orientation = splitPane.getOrientation();
        setCursor((orientation == JSplitPane.HORIZONTAL_SPLIT) ? Cursor.getPredefinedCursor(Cursor.E_RESIZE_CURSOR) : Cursor.getPredefinedCursor(Cursor.S_RESIZE_CURSOR));
        setBackground(UIManager.getColor("SplitPane.background"));
    }
    
    private void revalidate() {
        invalidate();
        if (splitPane != null) {
            splitPane.revalidate();
        }
    }
    
    public void setBasicSplitPaneUI(BasicSplitPaneUI newUI) {
        if (splitPane != null) {
            splitPane.removePropertyChangeListener(this);
            if (mouseHandler != null) {
                splitPane.removeMouseListener(mouseHandler);
                splitPane.removeMouseMotionListener(mouseHandler);
                removeMouseListener(mouseHandler);
                removeMouseMotionListener(mouseHandler);
                mouseHandler = null;
            }
        }
        splitPaneUI = newUI;
        if (newUI != null) {
            splitPane = newUI.getSplitPane();
            if (splitPane != null) {
                if (mouseHandler == null) mouseHandler = new BasicSplitPaneDivider$MouseHandler(this);
                splitPane.addMouseListener(mouseHandler);
                splitPane.addMouseMotionListener(mouseHandler);
                addMouseListener(mouseHandler);
                addMouseMotionListener(mouseHandler);
                splitPane.addPropertyChangeListener(this);
                if (splitPane.isOneTouchExpandable()) {
                    oneTouchExpandableChanged();
                }
            }
        } else {
            splitPane = null;
        }
    }
    
    public BasicSplitPaneUI getBasicSplitPaneUI() {
        return splitPaneUI;
    }
    
    public void setDividerSize(int newSize) {
        dividerSize = newSize;
    }
    
    public int getDividerSize() {
        return dividerSize;
    }
    
    public void setBorder(Border border) {
        Border oldBorder = this.border;
        this.border = border;
    }
    
    public Border getBorder() {
        return border;
    }
    
    public Insets getInsets() {
        Border border = getBorder();
        if (border != null) {
            return border.getBorderInsets(this);
        }
        return super.getInsets();
    }
    
    protected void setMouseOver(boolean mouseOver) {
        this.mouseOver = mouseOver;
    }
    
    public boolean isMouseOver() {
        return mouseOver;
    }
    
    public Dimension getPreferredSize() {
        if (orientation == JSplitPane.HORIZONTAL_SPLIT) {
            return new Dimension(getDividerSize(), 1);
        }
        return new Dimension(1, getDividerSize());
    }
    
    public Dimension getMinimumSize() {
        return getPreferredSize();
    }
    
    public void propertyChange(PropertyChangeEvent e) {
        if (e.getSource() == splitPane) {
            if (e.getPropertyName() == JSplitPane.ORIENTATION_PROPERTY) {
                orientation = splitPane.getOrientation();
                setCursor((orientation == JSplitPane.HORIZONTAL_SPLIT) ? Cursor.getPredefinedCursor(Cursor.E_RESIZE_CURSOR) : Cursor.getPredefinedCursor(Cursor.S_RESIZE_CURSOR));
                revalidate();
            } else if (e.getPropertyName() == JSplitPane.ONE_TOUCH_EXPANDABLE_PROPERTY) {
                oneTouchExpandableChanged();
            }
        }
    }
    
    public void paint(Graphics g) {
        super.paint(g);
        Border border = getBorder();
        if (border != null) {
            Dimension size = getSize();
            border.paintBorder(this, g, 0, 0, size.width, size.height);
        }
    }
    
    protected void oneTouchExpandableChanged() {
        if (!DefaultLookup.getBoolean(splitPane, splitPaneUI, "SplitPane.supportsOneTouchButtons", true)) {
            return;
        }
        if (splitPane.isOneTouchExpandable() && leftButton == null && rightButton == null) {
            leftButton = createLeftOneTouchButton();
            if (leftButton != null) leftButton.addActionListener(new BasicSplitPaneDivider$OneTouchActionHandler(this, true));
            rightButton = createRightOneTouchButton();
            if (rightButton != null) rightButton.addActionListener(new BasicSplitPaneDivider$OneTouchActionHandler(this, false));
            if (leftButton != null && rightButton != null) {
                add(leftButton);
                add(rightButton);
            }
        }
        revalidate();
    }
    
    protected JButton createLeftOneTouchButton() {
        JButton b = new BasicSplitPaneDivider$1(this);
        b.setMinimumSize(new Dimension(oneTouchSize, oneTouchSize));
        b.setCursor(Cursor.getPredefinedCursor(Cursor.DEFAULT_CURSOR));
        b.setFocusPainted(false);
        b.setBorderPainted(false);
        b.setRequestFocusEnabled(false);
        return b;
    }
    
    protected JButton createRightOneTouchButton() {
        JButton b = new BasicSplitPaneDivider$2(this);
        b.setMinimumSize(new Dimension(oneTouchSize, oneTouchSize));
        b.setCursor(Cursor.getPredefinedCursor(Cursor.DEFAULT_CURSOR));
        b.setFocusPainted(false);
        b.setBorderPainted(false);
        b.setRequestFocusEnabled(false);
        return b;
    }
    
    protected void prepareForDragging() {
        splitPaneUI.startDragging();
    }
    
    protected void dragDividerTo(int location) {
        splitPaneUI.dragDividerTo(location);
    }
    
    protected void finishDraggingTo(int location) {
        splitPaneUI.finishDraggingTo(location);
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
}
