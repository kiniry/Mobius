package javax.accessibility;

import java.util.*;
import java.awt.*;
import javax.swing.text.*;

public interface AccessibleHypertext extends AccessibleText {
    
    public abstract int getLinkCount();
    
    public abstract AccessibleHyperlink getLink(int linkIndex);
    
    public abstract int getLinkIndex(int charIndex);
}
