package java.awt;

import java.awt.event.KeyEvent;

public interface KeyEventPostProcessor {
    
    boolean postProcessKeyEvent(KeyEvent e);
}
