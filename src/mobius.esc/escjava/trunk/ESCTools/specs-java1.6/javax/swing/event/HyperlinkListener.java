package javax.swing.event;

import java.util.EventListener;

public interface HyperlinkListener extends EventListener {
    
    void hyperlinkUpdate(HyperlinkEvent e);
}
