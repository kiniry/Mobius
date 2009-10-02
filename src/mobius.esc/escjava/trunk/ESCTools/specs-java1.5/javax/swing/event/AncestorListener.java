package javax.swing.event;

import java.awt.event.*;
import java.awt.*;
import java.util.*;
import javax.swing.*;

public interface AncestorListener extends EventListener {
    
    public void ancestorAdded(AncestorEvent event);
    
    public void ancestorRemoved(AncestorEvent event);
    
    public void ancestorMoved(AncestorEvent event);
}
