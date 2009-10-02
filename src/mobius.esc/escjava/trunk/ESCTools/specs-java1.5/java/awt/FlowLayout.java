package java.awt;

import java.io.ObjectInputStream;
import java.io.IOException;

public class FlowLayout implements LayoutManager, java.io.Serializable {
    public static final int LEFT = 0;
    public static final int CENTER = 1;
    public static final int RIGHT = 2;
    public static final int LEADING = 3;
    public static final int TRAILING = 4;
    int align;
    int newAlign;
    int hgap;
    int vgap;
    private static final long serialVersionUID = -7262534875583282631L;
    
    public FlowLayout() {
        this(CENTER, 5, 5);
    }
    
    public FlowLayout(int align) {
        this(align, 5, 5);
    }
    
    public FlowLayout(int align, int hgap, int vgap) {
        
        this.hgap = hgap;
        this.vgap = vgap;
        setAlignment(align);
    }
    
    public int getAlignment() {
        return newAlign;
    }
    
    public void setAlignment(int align) {
        this.newAlign = align;
        switch (align) {
        case LEADING: 
            this.align = LEFT;
            break;
        
        case TRAILING: 
            this.align = RIGHT;
            break;
        
        default: 
            this.align = align;
            break;
        
        }
    }
    
    public int getHgap() {
        return hgap;
    }
    
    public void setHgap(int hgap) {
        this.hgap = hgap;
    }
    
    public int getVgap() {
        return vgap;
    }
    
    public void setVgap(int vgap) {
        this.vgap = vgap;
    }
    
    public void addLayoutComponent(String name, Component comp) {
    }
    
    public void removeLayoutComponent(Component comp) {
    }
    
    public Dimension preferredLayoutSize(Container target) {
        synchronized (target.getTreeLock()) {
            Dimension dim = new Dimension(0, 0);
            int nmembers = target.getComponentCount();
            boolean firstVisibleComponent = true;
            for (int i = 0; i < nmembers; i++) {
                Component m = target.getComponent(i);
                if (m.visible) {
                    Dimension d = m.getPreferredSize();
                    dim.height = Math.max(dim.height, d.height);
                    if (firstVisibleComponent) {
                        firstVisibleComponent = false;
                    } else {
                        dim.width += hgap;
                    }
                    dim.width += d.width;
                }
            }
            Insets insets = target.getInsets();
            dim.width += insets.left + insets.right + hgap * 2;
            dim.height += insets.top + insets.bottom + vgap * 2;
            return dim;
        }
    }
    
    public Dimension minimumLayoutSize(Container target) {
        synchronized (target.getTreeLock()) {
            Dimension dim = new Dimension(0, 0);
            int nmembers = target.getComponentCount();
            for (int i = 0; i < nmembers; i++) {
                Component m = target.getComponent(i);
                if (m.visible) {
                    Dimension d = m.getMinimumSize();
                    dim.height = Math.max(dim.height, d.height);
                    if (i > 0) {
                        dim.width += hgap;
                    }
                    dim.width += d.width;
                }
            }
            Insets insets = target.getInsets();
            dim.width += insets.left + insets.right + hgap * 2;
            dim.height += insets.top + insets.bottom + vgap * 2;
            return dim;
        }
    }
    
    private void moveComponents(Container target, int x, int y, int width, int height, int rowStart, int rowEnd, boolean ltr) {
        synchronized (target.getTreeLock()) {
            switch (newAlign) {
            case LEFT: 
                x += ltr ? 0 : width;
                break;
            
            case CENTER: 
                x += width / 2;
                break;
            
            case RIGHT: 
                x += ltr ? width : 0;
                break;
            
            case LEADING: 
                break;
            
            case TRAILING: 
                x += width;
                break;
            
            }
            for (int i = rowStart; i < rowEnd; i++) {
                Component m = target.getComponent(i);
                if (m.visible) {
                    if (ltr) {
                        m.setLocation(x, y + (height - m.height) / 2);
                    } else {
                        m.setLocation(target.width - x - m.width, y + (height - m.height) / 2);
                    }
                    x += m.width + hgap;
                }
            }
        }
    }
    
    public void layoutContainer(Container target) {
        synchronized (target.getTreeLock()) {
            Insets insets = target.getInsets();
            int maxwidth = target.width - (insets.left + insets.right + hgap * 2);
            int nmembers = target.getComponentCount();
            int x = 0;
            int y = insets.top + vgap;
            int rowh = 0;
            int start = 0;
            boolean ltr = target.getComponentOrientation().isLeftToRight();
            for (int i = 0; i < nmembers; i++) {
                Component m = target.getComponent(i);
                if (m.visible) {
                    Dimension d = m.getPreferredSize();
                    m.setSize(d.width, d.height);
                    if ((x == 0) || ((x + d.width) <= maxwidth)) {
                        if (x > 0) {
                            x += hgap;
                        }
                        x += d.width;
                        rowh = Math.max(rowh, d.height);
                    } else {
                        moveComponents(target, insets.left + hgap, y, maxwidth - x, rowh, start, i, ltr);
                        x = d.width;
                        y += vgap + rowh;
                        rowh = d.height;
                        start = i;
                    }
                }
            }
            moveComponents(target, insets.left + hgap, y, maxwidth - x, rowh, start, nmembers, ltr);
        }
    }
    private static final int currentSerialVersion = 1;
    private int serialVersionOnStream = currentSerialVersion;
    
    private void readObject(ObjectInputStream stream) throws IOException, ClassNotFoundException {
        stream.defaultReadObject();
        if (serialVersionOnStream < 1) {
            setAlignment(this.align);
        }
        serialVersionOnStream = currentSerialVersion;
    }
    
    public String toString() {
        String str = "";
        switch (align) {
        case LEFT: 
            str = ",align=left";
            break;
        
        case CENTER: 
            str = ",align=center";
            break;
        
        case RIGHT: 
            str = ",align=right";
            break;
        
        case LEADING: 
            str = ",align=leading";
            break;
        
        case TRAILING: 
            str = ",align=trailing";
            break;
        
        }
        return getClass().getName() + "[hgap=" + hgap + ",vgap=" + vgap + str + "]";
    }
}
