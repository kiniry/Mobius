package java.awt.event;

import java.util.EventListener;

public interface WindowFocusListener extends EventListener {
    
    public void windowGainedFocus(WindowEvent e);
    
    public void windowLostFocus(WindowEvent e);
}
