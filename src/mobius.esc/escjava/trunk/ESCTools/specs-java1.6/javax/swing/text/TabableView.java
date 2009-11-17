package javax.swing.text;

public interface TabableView {
    
    float getTabbedSpan(float x, TabExpander e);
    
    float getPartialSpan(int p0, int p1);
}
