package java.awt;

final class GraphicsCallback$PaintAllCallback extends GraphicsCallback {
    private static GraphicsCallback$PaintAllCallback instance = new GraphicsCallback$PaintAllCallback();
    
    private GraphicsCallback$PaintAllCallback() {
        
    }
    
    public void run(Component comp, Graphics cg) {
        comp.paintAll(cg);
    }
    
    static GraphicsCallback$PaintAllCallback getInstance() {
        return instance;
    }
}
