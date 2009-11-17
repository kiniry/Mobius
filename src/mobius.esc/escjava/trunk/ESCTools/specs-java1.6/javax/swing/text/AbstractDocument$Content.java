package javax.swing.text;

import java.util.*;
import java.io.*;
import javax.swing.undo.*;
import javax.swing.event.*;

public interface AbstractDocument$Content {
    
    public Position createPosition(int offset) throws BadLocationException;
    
    public int length();
    
    public UndoableEdit insertString(int where, String str) throws BadLocationException;
    
    public UndoableEdit remove(int where, int nitems) throws BadLocationException;
    
    public String getString(int where, int len) throws BadLocationException;
    
    public void getChars(int where, int len, Segment txt) throws BadLocationException;
}
