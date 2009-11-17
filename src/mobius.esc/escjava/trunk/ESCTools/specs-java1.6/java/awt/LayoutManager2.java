package java.awt;

public interface LayoutManager2 extends LayoutManager {
    
    void addLayoutComponent(Component comp, Object constraints);
    
    public Dimension maximumLayoutSize(Container target);
    
    public float getLayoutAlignmentX(Container target);
    
    public float getLayoutAlignmentY(Container target);
    
    public void invalidateLayout(Container target);
}
