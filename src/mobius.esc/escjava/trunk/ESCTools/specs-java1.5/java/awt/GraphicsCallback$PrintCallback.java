package java.awt;

final class GraphicsCallback$PrintCallback extends GraphicsCallback {
    private static GraphicsCallback$PrintCallback instance = new GraphicsCallback$PrintCallback();
    
    private GraphicsCallback$PrintCallback() {
        
    }
    
    public void run(Component comp, Graphics cg) {
        comp.print(cg);
    }
    
    static GraphicsCallback$PrintCallback getInstance() {
        return instance;
    }
}
