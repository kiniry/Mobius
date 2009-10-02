package javax.swing.text.html;

import java.util.*;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.swing.undo.*;

class HTMLDocument$FixedLengthDocument extends PlainDocument {
    private int maxLength;
    
    public HTMLDocument$FixedLengthDocument(int maxLength) {
        
        this.maxLength = maxLength;
    }
    
    public void insertString(int offset, String str, AttributeSet a) throws BadLocationException {
        if (str != null && str.length() + getLength() <= maxLength) {
            super.insertString(offset, str, a);
        }
    }
}
