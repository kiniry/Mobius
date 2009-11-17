package java.awt;

final class GraphicsCallback$PaintCallback extends GraphicsCallback {
    private static GraphicsCallback$PaintCallback instance = new GraphicsCallback$PaintCallback();
    
    private GraphicsCallback$PaintCallback() {
        
    }
    
    public void run(Component comp, Graphics cg) {
        comp.paint(cg);
    }
    
    static GraphicsCallback$PaintCallback getInstance() {
        return instance;
    }
}
