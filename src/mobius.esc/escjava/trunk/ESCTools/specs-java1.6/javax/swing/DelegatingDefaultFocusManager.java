package javax.swing;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.util.Set;

final class DelegatingDefaultFocusManager extends DefaultFocusManager {
    private final KeyboardFocusManager delegate;
    
    DelegatingDefaultFocusManager(KeyboardFocusManager delegate) {
        
        this.delegate = delegate;
        setDefaultFocusTraversalPolicy(gluePolicy);
    }
    
    KeyboardFocusManager getDelegate() {
        return delegate;
    }
    
    public void processKeyEvent(Component focusedComponent, KeyEvent e) {
        delegate.processKeyEvent(focusedComponent, e);
    }
    
    public void focusNextComponent(Component aComponent) {
        delegate.focusNextComponent(aComponent);
    }
    
    public void focusPreviousComponent(Component aComponent) {
        delegate.focusPreviousComponent(aComponent);
    }
    
    public Component getFocusOwner() {
        return delegate.getFocusOwner();
    }
    
    public void clearGlobalFocusOwner() {
        delegate.clearGlobalFocusOwner();
    }
    
    public Component getPermanentFocusOwner() {
        return delegate.getPermanentFocusOwner();
    }
    
    public Window getFocusedWindow() {
        return delegate.getFocusedWindow();
    }
    
    public Window getActiveWindow() {
        return delegate.getActiveWindow();
    }
    
    public FocusTraversalPolicy getDefaultFocusTraversalPolicy() {
        return delegate.getDefaultFocusTraversalPolicy();
    }
    
    public void setDefaultFocusTraversalPolicy(FocusTraversalPolicy defaultPolicy) {
        if (delegate != null) {
            delegate.setDefaultFocusTraversalPolicy(defaultPolicy);
        }
    }
    
    public void setDefaultFocusTraversalKeys(int id, Set keystrokes) {
        delegate.setDefaultFocusTraversalKeys(id, keystrokes);
    }
    
    public Set getDefaultFocusTraversalKeys(int id) {
        return delegate.getDefaultFocusTraversalKeys(id);
    }
    
    public Container getCurrentFocusCycleRoot() {
        return delegate.getCurrentFocusCycleRoot();
    }
    
    public void setGlobalCurrentFocusCycleRoot(Container newFocusCycleRoot) {
        delegate.setGlobalCurrentFocusCycleRoot(newFocusCycleRoot);
    }
    
    public void addPropertyChangeListener(PropertyChangeListener listener) {
        delegate.addPropertyChangeListener(listener);
    }
    
    public void removePropertyChangeListener(PropertyChangeListener listener) {
        delegate.removePropertyChangeListener(listener);
    }
    
    public void addPropertyChangeListener(String propertyName, PropertyChangeListener listener) {
        delegate.addPropertyChangeListener(propertyName, listener);
    }
    
    public void removePropertyChangeListener(String propertyName, PropertyChangeListener listener) {
        delegate.removePropertyChangeListener(propertyName, listener);
    }
    
    public void addVetoableChangeListener(VetoableChangeListener listener) {
        delegate.addVetoableChangeListener(listener);
    }
    
    public void removeVetoableChangeListener(VetoableChangeListener listener) {
        delegate.removeVetoableChangeListener(listener);
    }
    
    public void addVetoableChangeListener(String propertyName, VetoableChangeListener listener) {
        delegate.addVetoableChangeListener(propertyName, listener);
    }
    
    public void removeVetoableChangeListener(String propertyName, VetoableChangeListener listener) {
        delegate.removeVetoableChangeListener(propertyName, listener);
    }
    
    public void addKeyEventDispatcher(KeyEventDispatcher dispatcher) {
        delegate.addKeyEventDispatcher(dispatcher);
    }
    
    public void removeKeyEventDispatcher(KeyEventDispatcher dispatcher) {
        delegate.removeKeyEventDispatcher(dispatcher);
    }
    
    public boolean dispatchEvent(AWTEvent e) {
        return delegate.dispatchEvent(e);
    }
    
    public boolean dispatchKeyEvent(KeyEvent e) {
        return delegate.dispatchKeyEvent(e);
    }
    
    public void upFocusCycle(Component aComponent) {
        delegate.upFocusCycle(aComponent);
    }
    
    public void downFocusCycle(Container aContainer) {
        delegate.downFocusCycle(aContainer);
    }
}
