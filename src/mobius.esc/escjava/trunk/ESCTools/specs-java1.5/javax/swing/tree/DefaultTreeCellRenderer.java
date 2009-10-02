package javax.swing.tree;

import javax.swing.*;
import javax.swing.plaf.ColorUIResource;
import javax.swing.plaf.FontUIResource;
import javax.swing.plaf.basic.BasicGraphicsUtils;
import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.io.*;
import java.util.*;

public class DefaultTreeCellRenderer extends JLabel implements TreeCellRenderer {
    private JTree tree;
    protected boolean selected;
    protected boolean hasFocus;
    private boolean drawsFocusBorderAroundIcon;
    private boolean drawDashedFocusIndicator;
    private Color treeBGColor;
    private Color focusBGColor;
    protected transient Icon closedIcon;
    protected transient Icon leafIcon;
    protected transient Icon openIcon;
    protected Color textSelectionColor;
    protected Color textNonSelectionColor;
    protected Color backgroundSelectionColor;
    protected Color backgroundNonSelectionColor;
    protected Color borderSelectionColor;
    
    public DefaultTreeCellRenderer() {
        
        setHorizontalAlignment(JLabel.LEFT);
        setLeafIcon(UIManager.getIcon("Tree.leafIcon"));
        setClosedIcon(UIManager.getIcon("Tree.closedIcon"));
        setOpenIcon(UIManager.getIcon("Tree.openIcon"));
        setTextSelectionColor(UIManager.getColor("Tree.selectionForeground"));
        setTextNonSelectionColor(UIManager.getColor("Tree.textForeground"));
        setBackgroundSelectionColor(UIManager.getColor("Tree.selectionBackground"));
        setBackgroundNonSelectionColor(UIManager.getColor("Tree.textBackground"));
        setBorderSelectionColor(UIManager.getColor("Tree.selectionBorderColor"));
        Object value = UIManager.get("Tree.drawsFocusBorderAroundIcon");
        drawsFocusBorderAroundIcon = (value != null && ((Boolean)(Boolean)value).booleanValue());
        value = UIManager.get("Tree.drawDashedFocusIndicator");
        drawDashedFocusIndicator = (value != null && ((Boolean)(Boolean)value).booleanValue());
    }
    
    public Icon getDefaultOpenIcon() {
        return UIManager.getIcon("Tree.openIcon");
    }
    
    public Icon getDefaultClosedIcon() {
        return UIManager.getIcon("Tree.closedIcon");
    }
    
    public Icon getDefaultLeafIcon() {
        return UIManager.getIcon("Tree.leafIcon");
    }
    
    public void setOpenIcon(Icon newIcon) {
        openIcon = newIcon;
    }
    
    public Icon getOpenIcon() {
        return openIcon;
    }
    
    public void setClosedIcon(Icon newIcon) {
        closedIcon = newIcon;
    }
    
    public Icon getClosedIcon() {
        return closedIcon;
    }
    
    public void setLeafIcon(Icon newIcon) {
        leafIcon = newIcon;
    }
    
    public Icon getLeafIcon() {
        return leafIcon;
    }
    
    public void setTextSelectionColor(Color newColor) {
        textSelectionColor = newColor;
    }
    
    public Color getTextSelectionColor() {
        return textSelectionColor;
    }
    
    public void setTextNonSelectionColor(Color newColor) {
        textNonSelectionColor = newColor;
    }
    
    public Color getTextNonSelectionColor() {
        return textNonSelectionColor;
    }
    
    public void setBackgroundSelectionColor(Color newColor) {
        backgroundSelectionColor = newColor;
    }
    
    public Color getBackgroundSelectionColor() {
        return backgroundSelectionColor;
    }
    
    public void setBackgroundNonSelectionColor(Color newColor) {
        backgroundNonSelectionColor = newColor;
    }
    
    public Color getBackgroundNonSelectionColor() {
        return backgroundNonSelectionColor;
    }
    
    public void setBorderSelectionColor(Color newColor) {
        borderSelectionColor = newColor;
    }
    
    public Color getBorderSelectionColor() {
        return borderSelectionColor;
    }
    
    public void setFont(Font font) {
        if (font instanceof FontUIResource) font = null;
        super.setFont(font);
    }
    
    public Font getFont() {
        Font font = super.getFont();
        if (font == null && tree != null) {
            font = tree.getFont();
        }
        return font;
    }
    
    public void setBackground(Color color) {
        if (color instanceof ColorUIResource) color = null;
        super.setBackground(color);
    }
    
    public Component getTreeCellRendererComponent(JTree tree, Object value, boolean sel, boolean expanded, boolean leaf, int row, boolean hasFocus) {
        String stringValue = tree.convertValueToText(value, sel, expanded, leaf, row, hasFocus);
        this.tree = tree;
        this.hasFocus = hasFocus;
        setText(stringValue);
        if (sel) setForeground(getTextSelectionColor()); else setForeground(getTextNonSelectionColor());
        if (!tree.isEnabled()) {
            setEnabled(false);
            if (leaf) {
                setDisabledIcon(getLeafIcon());
            } else if (expanded) {
                setDisabledIcon(getOpenIcon());
            } else {
                setDisabledIcon(getClosedIcon());
            }
        } else {
            setEnabled(true);
            if (leaf) {
                setIcon(getLeafIcon());
            } else if (expanded) {
                setIcon(getOpenIcon());
            } else {
                setIcon(getClosedIcon());
            }
        }
        setComponentOrientation(tree.getComponentOrientation());
        selected = sel;
        return this;
    }
    
    public void paint(Graphics g) {
        Color bColor;
        if (selected) {
            bColor = getBackgroundSelectionColor();
        } else {
            bColor = getBackgroundNonSelectionColor();
            if (bColor == null) bColor = getBackground();
        }
        int imageOffset = -1;
        if (bColor != null) {
            Icon currentI = getIcon();
            imageOffset = getLabelStart();
            g.setColor(bColor);
            if (getComponentOrientation().isLeftToRight()) {
                g.fillRect(imageOffset, 0, getWidth() - imageOffset, getHeight());
            } else {
                g.fillRect(0, 0, getWidth() - imageOffset, getHeight());
            }
        }
        if (hasFocus) {
            if (drawsFocusBorderAroundIcon) {
                imageOffset = 0;
            } else if (imageOffset == -1) {
                imageOffset = getLabelStart();
            }
            if (getComponentOrientation().isLeftToRight()) {
                paintFocus(g, imageOffset, 0, getWidth() - imageOffset, getHeight());
            } else {
                paintFocus(g, 0, 0, getWidth() - imageOffset, getHeight());
            }
        }
        super.paint(g);
    }
    
    private void paintFocus(Graphics g, int x, int y, int w, int h) {
        Color bsColor = getBorderSelectionColor();
        if (bsColor != null && (selected || !drawDashedFocusIndicator)) {
            g.setColor(bsColor);
            g.drawRect(x, y, w - 1, h - 1);
        }
        if (drawDashedFocusIndicator) {
            Color color;
            if (selected) {
                color = getBackgroundSelectionColor();
            } else {
                color = getBackgroundNonSelectionColor();
                if (color == null) {
                    color = getBackground();
                }
            }
            if (treeBGColor != color) {
                treeBGColor = color;
                focusBGColor = new Color(~color.getRGB());
            }
            g.setColor(focusBGColor);
            BasicGraphicsUtils.drawDashedRect(g, x, y, w, h);
        }
    }
    
    private int getLabelStart() {
        Icon currentI = getIcon();
        if (currentI != null && getText() != null) {
            return currentI.getIconWidth() + Math.max(0, getIconTextGap() - 1);
        }
        return 0;
    }
    
    public Dimension getPreferredSize() {
        Dimension retDimension = super.getPreferredSize();
        if (retDimension != null) retDimension = new Dimension(retDimension.width + 3, retDimension.height);
        return retDimension;
    }
    
    public void validate() {
    }
    
    public void invalidate() {
    }
    
    public void revalidate() {
    }
    
    public void repaint(long tm, int x, int y, int width, int height) {
    }
    
    public void repaint(Rectangle r) {
    }
    
    public void repaint() {
    }
    
    protected void firePropertyChange(String propertyName, Object oldValue, Object newValue) {
        if (propertyName == "text") super.firePropertyChange(propertyName, oldValue, newValue);
    }
    
    public void firePropertyChange(String propertyName, byte oldValue, byte newValue) {
    }
    
    public void firePropertyChange(String propertyName, char oldValue, char newValue) {
    }
    
    public void firePropertyChange(String propertyName, short oldValue, short newValue) {
    }
    
    public void firePropertyChange(String propertyName, int oldValue, int newValue) {
    }
    
    public void firePropertyChange(String propertyName, long oldValue, long newValue) {
    }
    
    public void firePropertyChange(String propertyName, float oldValue, float newValue) {
    }
    
    public void firePropertyChange(String propertyName, double oldValue, double newValue) {
    }
    
    public void firePropertyChange(String propertyName, boolean oldValue, boolean newValue) {
    }
}
