package java.awt;

final class GraphicsCallback$PrintAllCallback extends GraphicsCallback {
    private static GraphicsCallback$PrintAllCallback instance = new GraphicsCallback$PrintAllCallback();
    
    private GraphicsCallback$PrintAllCallback() {
        
    }
    
    public void run(Component comp, Graphics cg) {
        comp.printAll(cg);
    }
    
    static GraphicsCallback$PrintAllCallback getInstance() {
        return instance;
    }
}
