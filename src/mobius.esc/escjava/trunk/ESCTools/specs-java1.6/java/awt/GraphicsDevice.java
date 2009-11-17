package java.awt;

import java.awt.image.ColorModel;

public abstract class GraphicsDevice {
    private Window fullScreenWindow;
    private Rectangle windowedModeBounds;
    
    protected GraphicsDevice() {
        
    }
    public static final int TYPE_RASTER_SCREEN = 0;
    public static final int TYPE_PRINTER = 1;
    public static final int TYPE_IMAGE_BUFFER = 2;
    
    public abstract int getType();
    
    public abstract String getIDstring();
    
    public abstract GraphicsConfiguration[] getConfigurations();
    
    public abstract GraphicsConfiguration getDefaultConfiguration();
    
    public GraphicsConfiguration getBestConfiguration(GraphicsConfigTemplate gct) {
        GraphicsConfiguration[] configs = getConfigurations();
        return gct.getBestConfiguration(configs);
    }
    
    public boolean isFullScreenSupported() {
        return false;
    }
    
    public void setFullScreenWindow(Window w) {
        DisplayMode dm;
        if (w == null) {
            dm = null;
        } else {
            dm = getDisplayMode();
        }
        if (fullScreenWindow != null && windowedModeBounds != null) {
            fullScreenWindow.setBounds(windowedModeBounds);
        }
        fullScreenWindow = w;
        if (fullScreenWindow != null) {
            windowedModeBounds = fullScreenWindow.getBounds();
            fullScreenWindow.setBounds(0, 0, dm.getWidth(), dm.getHeight());
            fullScreenWindow.setVisible(true);
            fullScreenWindow.toFront();
        }
    }
    
    public Window getFullScreenWindow() {
        return fullScreenWindow;
    }
    
    public boolean isDisplayChangeSupported() {
        return false;
    }
    
    public void setDisplayMode(DisplayMode dm) {
        throw new UnsupportedOperationException("Cannot change display mode");
    }
    
    public DisplayMode getDisplayMode() {
        GraphicsConfiguration gc = getDefaultConfiguration();
        Rectangle r = gc.getBounds();
        ColorModel cm = gc.getColorModel();
        return new DisplayMode(r.width, r.height, cm.getPixelSize(), 0);
    }
    
    public DisplayMode[] getDisplayModes() {
        return new DisplayMode[]{getDisplayMode()};
    }
    
    public int getAvailableAcceleratedMemory() {
        return -1;
    }
}
