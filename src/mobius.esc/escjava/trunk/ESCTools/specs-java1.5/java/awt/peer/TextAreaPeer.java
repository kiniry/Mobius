package java.awt.peer;

import java.awt.Dimension;

public interface TextAreaPeer extends TextComponentPeer {
    
    void insert(String text, int pos);
    
    void replaceRange(String text, int start, int end);
    
    Dimension getPreferredSize(int rows, int columns);
    
    Dimension getMinimumSize(int rows, int columns);
    
    void insertText(String txt, int pos);
    
    void replaceText(String txt, int start, int end);
    
    Dimension preferredSize(int rows, int cols);
    
    Dimension minimumSize(int rows, int cols);
}
