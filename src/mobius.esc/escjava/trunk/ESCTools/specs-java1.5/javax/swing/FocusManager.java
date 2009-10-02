package javax.swing;

import java.awt.*;

public abstract class FocusManager extends DefaultKeyboardFocusManager {
    
    public FocusManager() {
        
    }
    public static final String FOCUS_MANAGER_CLASS_PROPERTY = "FocusManagerClassName";
    private static boolean enabled = true;
    
    public static FocusManager getCurrentManager() {
        KeyboardFocusManager manager = KeyboardFocusManager.getCurrentKeyboardFocusManager();
        if (manager instanceof FocusManager) {
            return (FocusManager)(FocusManager)manager;
        } else {
            return new DelegatingDefaultFocusManager(manager);
        }
    }
    
    public static void setCurrentManager(FocusManager aFocusManager) throws SecurityException {
        KeyboardFocusManager toSet = (aFocusManager instanceof DelegatingDefaultFocusManager) ? ((DelegatingDefaultFocusManager)(DelegatingDefaultFocusManager)aFocusManager).getDelegate() : aFocusManager;
        KeyboardFocusManager.setCurrentKeyboardFocusManager(toSet);
    }
    
    
    public static void disableSwingFocusManager() {
        if (enabled) {
            enabled = false;
            KeyboardFocusManager.getCurrentKeyboardFocusManager().setDefaultFocusTraversalPolicy(new DefaultFocusTraversalPolicy());
        }
    }
    
    
    public static boolean isFocusManagerEnabled() {
        return enabled;
    }
}
