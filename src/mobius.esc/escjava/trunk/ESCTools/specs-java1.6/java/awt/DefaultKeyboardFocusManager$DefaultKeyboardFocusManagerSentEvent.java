package java.awt;

import java.util.logging.*;
import sun.awt.AppContext;

class DefaultKeyboardFocusManager$DefaultKeyboardFocusManagerSentEvent extends SentEvent {
    
    public DefaultKeyboardFocusManager$DefaultKeyboardFocusManagerSentEvent(AWTEvent nested, AppContext toNotify) {
        super(nested, toNotify);
    }
    
    public final void dispatch() {
        KeyboardFocusManager manager = KeyboardFocusManager.getCurrentKeyboardFocusManager();
        DefaultKeyboardFocusManager defaultManager = (manager instanceof DefaultKeyboardFocusManager) ? (DefaultKeyboardFocusManager)(DefaultKeyboardFocusManager)manager : null;
        if (defaultManager != null) {
            synchronized (defaultManager) {
                DefaultKeyboardFocusManager.access$008(defaultManager);
            }
        }
        super.dispatch();
        if (defaultManager != null) {
            synchronized (defaultManager) {
                DefaultKeyboardFocusManager.access$010(defaultManager);
            }
        }
    }
}
