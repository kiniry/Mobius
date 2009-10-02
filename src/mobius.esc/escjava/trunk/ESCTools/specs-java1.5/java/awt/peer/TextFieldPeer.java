package java.awt.peer;

import java.awt.Dimension;

public interface TextFieldPeer extends TextComponentPeer {
    
    void setEchoChar(char echoChar);
    
    Dimension getPreferredSize(int columns);
    
    Dimension getMinimumSize(int columns);
    
    void setEchoCharacter(char c);
    
    Dimension preferredSize(int cols);
    
    Dimension minimumSize(int cols);
}
