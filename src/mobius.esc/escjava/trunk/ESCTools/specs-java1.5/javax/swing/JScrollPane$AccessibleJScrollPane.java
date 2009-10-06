package javax.swing;

import javax.swing.plaf.*;
import javax.swing.border.*;
import javax.swing.event.*;
import javax.accessibility.*;
import java.beans.*;

public class JScrollPane$AccessibleJScrollPane extends JComponent$AccessibleJComponent implements ChangeListener, PropertyChangeListener {
    /*synthetic*/ final JScrollPane this$0;
    protected JViewport viewPort = null;
    
    public void resetViewPort() {
        if (viewPort != null) {
            viewPort.removeChangeListener(this);
            viewPort.removePropertyChangeListener(this);
        }
        viewPort = this$0.getViewport();
        if (viewPort != null) {
            viewPort.addChangeListener(this);
            viewPort.addPropertyChangeListener(this);
        }
    }
    
    public JScrollPane$AccessibleJScrollPane(/*synthetic*/ final JScrollPane this$0) {
        super(this$0);
        this.this$0 = this$0;
        resetViewPort();
        JScrollBar scrollBar = this$0.getHorizontalScrollBar();
        if (scrollBar != null) {
            setScrollBarRelations(scrollBar);
        }
        scrollBar = this$0.getVerticalScrollBar();
        if (scrollBar != null) {
            setScrollBarRelations(scrollBar);
        }
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.SCROLL_PANE;
    }
    
    public void stateChanged(ChangeEvent e) {
        if (e == null) {
            throw new NullPointerException();
        }
        firePropertyChange(ACCESSIBLE_VISIBLE_DATA_PROPERTY, Boolean.valueOf(false), Boolean.valueOf(true));
    }
    
    public void propertyChange(PropertyChangeEvent e) {
        String propertyName = e.getPropertyName();
        if (propertyName == "horizontalScrollBar" || propertyName == "verticalScrollBar") {
            if (e.getNewValue() instanceof JScrollBar) {
                setScrollBarRelations((JScrollBar)(JScrollBar)e.getNewValue());
            }
        }
    }
    
    void setScrollBarRelations(JScrollBar scrollBar) {
        AccessibleRelation controlledBy = new AccessibleRelation(AccessibleRelation.CONTROLLED_BY, scrollBar);
        AccessibleRelation controllerFor = new AccessibleRelation(AccessibleRelation.CONTROLLER_FOR, this$0);
        AccessibleContext ac = scrollBar.getAccessibleContext();
        ac.getAccessibleRelationSet().add(controllerFor);
        getAccessibleRelationSet().add(controlledBy);
    }
}
