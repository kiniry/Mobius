package java.awt.event;

import java.util.EventListener;

public interface ContainerListener extends EventListener {
    
    public void componentAdded(ContainerEvent e);
    
    public void componentRemoved(ContainerEvent e);
}
