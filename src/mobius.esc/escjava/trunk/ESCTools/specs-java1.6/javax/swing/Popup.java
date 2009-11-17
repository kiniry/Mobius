package javax.swing;

import java.awt.*;

public class Popup {
    private Component component;
    
    protected Popup(Component owner, Component contents, int x, int y) {
        this();
        if (contents == null) {
            throw new IllegalArgumentException("Contents must be non-null");
        }
        reset(owner, contents, x, y);
    }
    
    protected Popup() {
        
    }
    
    public void show() {
        Component component = getComponent();
        if (component != null) {
            component.show();
        }
    }
    
    public void hide() {
        Component component = getComponent();
        if (component instanceof JWindow) {
            component.hide();
            ((JWindow)(JWindow)component).getContentPane().removeAll();
        }
        dispose();
    }
    
    void dispose() {
        Component component = getComponent();
        if (component instanceof JWindow) {
            ((Window)(Window)component).dispose();
            component = null;
        }
    }
    
    void reset(Component owner, Component contents, int ownerX, int ownerY) {
        if (getComponent() == null) {
            component = createComponent(owner);
        }
        Component c = getComponent();
        if (c instanceof JWindow) {
            JWindow component = (JWindow)(JWindow)getComponent();
            component.setLocation(ownerX, ownerY);
            component.getContentPane().add(contents, BorderLayout.CENTER);
            contents.invalidate();
            if (component.isVisible()) {
                pack();
            }
        }
    }
    
    void pack() {
        Component component = getComponent();
        if (component instanceof Window) {
            ((Window)(Window)component).pack();
        }
    }
    
    private Window getParentWindow(Component owner) {
        Window window = null;
        if (owner instanceof Window) {
            window = (Window)(Window)owner;
        } else if (owner != null) {
            window = SwingUtilities.getWindowAncestor(owner);
        }
        if (window == null) {
            window = new Popup$DefaultFrame();
        }
        return window;
    }
    
    Component createComponent(Component owner) {
        if (GraphicsEnvironment.isHeadless()) {
            return null;
        }
        return new Popup$HeavyWeightWindow(getParentWindow(owner));
    }
    
    Component getComponent() {
        return component;
    }
    {
    }
    {
    }
}
