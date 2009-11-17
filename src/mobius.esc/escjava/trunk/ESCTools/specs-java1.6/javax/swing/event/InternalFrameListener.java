package javax.swing.event;

import java.util.EventListener;

public interface InternalFrameListener extends EventListener {
    
    public void internalFrameOpened(InternalFrameEvent e);
    
    public void internalFrameClosing(InternalFrameEvent e);
    
    public void internalFrameClosed(InternalFrameEvent e);
    
    public void internalFrameIconified(InternalFrameEvent e);
    
    public void internalFrameDeiconified(InternalFrameEvent e);
    
    public void internalFrameActivated(InternalFrameEvent e);
    
    public void internalFrameDeactivated(InternalFrameEvent e);
}
