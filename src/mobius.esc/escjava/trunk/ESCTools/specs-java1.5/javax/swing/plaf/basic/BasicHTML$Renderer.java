package javax.swing.plaf.basic;

import java.io.*;
import java.awt.*;
import javax.swing.*;
import javax.swing.text.*;
import javax.swing.text.html.*;

class BasicHTML$Renderer extends View {
    
    BasicHTML$Renderer(JComponent c, ViewFactory f, View v) {
        super(null);
        host = c;
        factory = f;
        view = v;
        view.setParent(this);
        setSize(view.getPreferredSpan(X_AXIS), view.getPreferredSpan(Y_AXIS));
    }
    
    public AttributeSet getAttributes() {
        return null;
    }
    
    public float getPreferredSpan(int axis) {
        if (axis == X_AXIS) {
            return width;
        }
        return view.getPreferredSpan(axis);
    }
    
    public float getMinimumSpan(int axis) {
        return view.getMinimumSpan(axis);
    }
    
    public float getMaximumSpan(int axis) {
        return Integer.MAX_VALUE;
    }
    
    public void preferenceChanged(View child, boolean width, boolean height) {
        host.revalidate();
        host.repaint();
    }
    
    public float getAlignment(int axis) {
        return view.getAlignment(axis);
    }
    
    public void paint(Graphics g, Shape allocation) {
        Rectangle alloc = allocation.getBounds();
        view.setSize(alloc.width, alloc.height);
        view.paint(g, allocation);
    }
    
    public void setParent(View parent) {
        throw new Error("Can\'t set parent on root view");
    }
    
    public int getViewCount() {
        return 1;
    }
    
    public View getView(int n) {
        return view;
    }
    
    public Shape modelToView(int pos, Shape a, Position$Bias b) throws BadLocationException {
        return view.modelToView(pos, a, b);
    }
    
    public Shape modelToView(int p0, Position$Bias b0, int p1, Position$Bias b1, Shape a) throws BadLocationException {
        return view.modelToView(p0, b0, p1, b1, a);
    }
    
    public int viewToModel(float x, float y, Shape a, Position$Bias[] bias) {
        return view.viewToModel(x, y, a, bias);
    }
    
    public Document getDocument() {
        return view.getDocument();
    }
    
    public int getStartOffset() {
        return view.getStartOffset();
    }
    
    public int getEndOffset() {
        return view.getEndOffset();
    }
    
    public Element getElement() {
        return view.getElement();
    }
    
    public void setSize(float width, float height) {
        this.width = (int)width;
        view.setSize(width, height);
    }
    
    public Container getContainer() {
        return host;
    }
    
    public ViewFactory getViewFactory() {
        return factory;
    }
    private int width;
    private View view;
    private ViewFactory factory;
    private JComponent host;
}
