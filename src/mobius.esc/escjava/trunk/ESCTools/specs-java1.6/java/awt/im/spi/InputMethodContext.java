package java.awt.im.spi;

import java.awt.Window;
import java.awt.font.TextHitInfo;
import java.awt.im.InputMethodRequests;
import java.text.AttributedCharacterIterator;
import javax.swing.JFrame;

public interface InputMethodContext extends InputMethodRequests {
    
    public void dispatchInputMethodEvent(int id, AttributedCharacterIterator text, int committedCharacterCount, TextHitInfo caret, TextHitInfo visiblePosition);
    
    public Window createInputMethodWindow(String title, boolean attachToInputContext);
    
    public JFrame createInputMethodJFrame(String title, boolean attachToInputContext);
    
    public void enableClientWindowNotification(InputMethod inputMethod, boolean enable);
}
