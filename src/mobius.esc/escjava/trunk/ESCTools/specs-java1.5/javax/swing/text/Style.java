package javax.swing.text;

import javax.swing.event.ChangeListener;

public interface Style extends MutableAttributeSet {
    
    public String getName();
    
    public void addChangeListener(ChangeListener l);
    
    public void removeChangeListener(ChangeListener l);
}
