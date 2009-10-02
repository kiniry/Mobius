package javax.swing.text;

import java.util.*;
import java.io.*;
import javax.swing.undo.*;
import javax.swing.event.*;

public interface AbstractDocument$AttributeContext {
    
    public AttributeSet addAttribute(AttributeSet old, Object name, Object value);
    
    public AttributeSet addAttributes(AttributeSet old, AttributeSet attr);
    
    public AttributeSet removeAttribute(AttributeSet old, Object name);
    
    public AttributeSet removeAttributes(AttributeSet old, Enumeration names);
    
    public AttributeSet removeAttributes(AttributeSet old, AttributeSet attrs);
    
    public AttributeSet getEmptySet();
    
    public void reclaim(AttributeSet a);
}
