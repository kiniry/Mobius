package java.awt.peer;

import java.awt.Rectangle;
import java.awt.im.InputMethodRequests;

public interface TextComponentPeer extends ComponentPeer {
    
    void setEditable(boolean editable);
    
    String getText();
    
    void setText(String l);
    
    int getSelectionStart();
    
    int getSelectionEnd();
    
    void select(int selStart, int selEnd);
    
    void setCaretPosition(int pos);
    
    int getCaretPosition();
    
    int getIndexAtPoint(int x, int y);
    
    Rectangle getCharacterBounds(int i);
    
    long filterEvents(long mask);
    
    InputMethodRequests getInputMethodRequests();
}
