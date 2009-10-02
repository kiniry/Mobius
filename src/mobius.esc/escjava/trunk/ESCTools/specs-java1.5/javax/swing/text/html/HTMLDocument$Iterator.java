package javax.swing.text.html;

import java.util.*;
import java.io.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.swing.undo.*;

public abstract class HTMLDocument$Iterator {
    
    public HTMLDocument$Iterator() {
        
    }
    
    public abstract AttributeSet getAttributes();
    
    public abstract int getStartOffset();
    
    public abstract int getEndOffset();
    
    public abstract void next();
    
    public abstract boolean isValid();
    
    public abstract HTML$Tag getTag();
}
