package java.awt;

import java.util.logging.*;

public class ContainerOrderFocusTraversalPolicy extends FocusTraversalPolicy implements java.io.Serializable {
    
    public ContainerOrderFocusTraversalPolicy() {
        
    }
    private static final MutableBoolean found = new MutableBoolean();
    private static final Logger log = Logger.getLogger("java.awt.ContainerOrderFocusTraversalPolicy");
    private static final long serialVersionUID = 486933713763926351L;
    private boolean implicitDownCycleTraversal = true;
    
    public Component getComponentAfter(Container aContainer, Component aComponent) {
        if (log.isLoggable(Level.FINE)) log.fine("Looking for next component in " + aContainer + " for " + aComponent);
        if (aContainer == null || aComponent == null) {
            throw new IllegalArgumentException("aContainer and aComponent cannot be null");
        }
        if (!aContainer.isFocusTraversalPolicyProvider() && !aContainer.isFocusCycleRoot()) {
            throw new IllegalArgumentException("aContainer should be focus cycle root or focus traversal policy provider");
        } else if (aContainer.isFocusCycleRoot() && !aComponent.isFocusCycleRoot(aContainer)) {
            throw new IllegalArgumentException("aContainer is not a focus cycle root of aComponent");
        }
        synchronized (aContainer.getTreeLock()) {
            found.value = false;
            Component retval = getComponentAfter(aContainer, aComponent, found);
            if (retval != null) {
                if (log.isLoggable(Level.FINE)) log.fine("After component is " + retval);
                return retval;
            } else if (found.value) {
                if (log.isLoggable(Level.FINE)) log.fine("Didn\'t find next component in " + aContainer + " - falling back to the first ");
                return getFirstComponent(aContainer);
            } else {
                if (log.isLoggable(Level.FINE)) log.fine("After component is null");
                return null;
            }
        }
    }
    
    private Component getComponentAfter(Container aContainer, Component aComponent, MutableBoolean found) {
        if (!(aContainer.isVisible() && aContainer.isDisplayable())) {
            return null;
        }
        if (found.value) {
            if (accept(aContainer)) {
                return aContainer;
            }
        } else if (aContainer == aComponent) {
            found.value = true;
        }
        for (int i = 0; i < aContainer.ncomponents; i++) {
            Component comp = aContainer.component[i];
            if ((comp instanceof Container) && !((Container)(Container)comp).isFocusCycleRoot()) {
                Component retval = null;
                if (((Container)(Container)comp).isFocusTraversalPolicyProvider()) {
                    if (log.isLoggable(Level.FINE)) log.fine("Entering FTP " + comp);
                    Container cont = (Container)(Container)comp;
                    FocusTraversalPolicy policy = cont.getFocusTraversalPolicy();
                    if (log.isLoggable(Level.FINE)) log.fine("FTP contains " + aComponent + ": " + cont.isAncestorOf(aComponent));
                    if (found.value) {
                        retval = policy.getDefaultComponent(cont);
                        if (log.isLoggable(Level.FINE)) log.fine("Used FTP for getting default component: " + retval);
                    } else {
                        found.value = cont.isAncestorOf(aComponent);
                        if (found.value) {
                            if (aComponent == policy.getLastComponent(cont)) {
                                retval = null;
                            } else {
                                retval = policy.getComponentAfter(cont, aComponent);
                                if (log.isLoggable(Level.FINE)) log.fine("FTP found next for the component : " + retval);
                            }
                        }
                    }
                } else {
                    retval = getComponentAfter((Container)(Container)comp, aComponent, found);
                }
                if (retval != null) {
                    return retval;
                }
            } else if (found.value) {
                if (accept(comp)) {
                    return comp;
                }
            } else if (comp == aComponent) {
                found.value = true;
            }
            if (found.value && getImplicitDownCycleTraversal() && (comp instanceof Container) && ((Container)(Container)comp).isFocusCycleRoot()) {
                Container cont = (Container)(Container)comp;
                Component retval = cont.getFocusTraversalPolicy().getDefaultComponent(cont);
                if (retval != null) {
                    return retval;
                }
            }
        }
        return null;
    }
    
    public Component getComponentBefore(Container aContainer, Component aComponent) {
        if (aContainer == null || aComponent == null) {
            throw new IllegalArgumentException("aContainer and aComponent cannot be null");
        }
        if (!aContainer.isFocusTraversalPolicyProvider() && !aContainer.isFocusCycleRoot()) {
            throw new IllegalArgumentException("aContainer should be focus cycle root or focus traversal policy provider");
        } else if (aContainer.isFocusCycleRoot() && !aComponent.isFocusCycleRoot(aContainer)) {
            throw new IllegalArgumentException("aContainer is not a focus cycle root of aComponent");
        }
        synchronized (aContainer.getTreeLock()) {
            found.value = false;
            Component retval = getComponentBefore(aContainer, aComponent, found);
            if (retval != null) {
                if (log.isLoggable(Level.FINE)) log.fine("Before component is " + retval);
                return retval;
            } else if (found.value) {
                if (log.isLoggable(Level.FINE)) log.fine("Didn\'t find before component in " + aContainer + " - falling back to the first ");
                return getLastComponent(aContainer);
            } else {
                if (log.isLoggable(Level.FINE)) log.fine("Before component is null");
                return null;
            }
        }
    }
    
    private Component getComponentBefore(Container aContainer, Component aComponent, MutableBoolean found) {
        if (!(aContainer.isVisible() && aContainer.isDisplayable())) {
            return null;
        }
        for (int i = aContainer.ncomponents - 1; i >= 0; i--) {
            Component comp = aContainer.component[i];
            if (comp == aComponent) {
                found.value = true;
            } else if ((comp instanceof Container) && !((Container)(Container)comp).isFocusCycleRoot()) {
                Component retval = null;
                if (((Container)(Container)comp).isFocusTraversalPolicyProvider()) {
                    if (log.isLoggable(Level.FINE)) log.fine("Entering FTP " + comp);
                    Container cont = (Container)(Container)comp;
                    FocusTraversalPolicy policy = cont.getFocusTraversalPolicy();
                    if (log.isLoggable(Level.FINE)) log.fine("FTP contains " + aComponent + ": " + cont.isAncestorOf(aComponent));
                    if (found.value) {
                        retval = policy.getLastComponent(cont);
                        if (log.isLoggable(Level.FINE)) log.fine("Used FTP for getting last component: " + retval);
                    } else {
                        found.value = cont.isAncestorOf(aComponent);
                        if (found.value) {
                            if (aComponent == policy.getFirstComponent(cont)) {
                                retval = null;
                            } else {
                                retval = policy.getComponentBefore(cont, aComponent);
                                if (log.isLoggable(Level.FINE)) log.fine("FTP found previous for the component : " + retval);
                            }
                        }
                    }
                } else {
                    retval = getComponentBefore((Container)(Container)comp, aComponent, found);
                }
                if (retval != null) {
                    return retval;
                }
            } else if (found.value) {
                if (accept(comp)) {
                    return comp;
                }
            }
        }
        if (found.value) {
            if (accept(aContainer)) {
                return aContainer;
            }
        } else if (aContainer == aComponent) {
            found.value = true;
        }
        return null;
    }
    
    public Component getFirstComponent(Container aContainer) {
        if (aContainer == null) {
            throw new IllegalArgumentException("aContainer cannot be null");
        }
        synchronized (aContainer.getTreeLock()) {
            if (!(aContainer.isVisible() && aContainer.isDisplayable())) {
                return null;
            }
            if (accept(aContainer)) {
                return aContainer;
            }
            for (int i = 0; i < aContainer.ncomponents; i++) {
                Component comp = aContainer.component[i];
                if (comp instanceof Container && !((Container)(Container)comp).isFocusCycleRoot()) {
                    Component retval = null;
                    Container cont = (Container)(Container)comp;
                    if (cont.isFocusTraversalPolicyProvider()) {
                        FocusTraversalPolicy policy = cont.getFocusTraversalPolicy();
                        retval = policy.getDefaultComponent(cont);
                    } else {
                        retval = getFirstComponent((Container)(Container)comp);
                    }
                    if (retval != null) {
                        return retval;
                    }
                } else if (accept(comp)) {
                    return comp;
                }
            }
        }
        return null;
    }
    
    public Component getLastComponent(Container aContainer) {
        if (aContainer == null) {
            throw new IllegalArgumentException("aContainer cannot be null");
        }
        if (log.isLoggable(Level.FINE)) log.fine("Looking for the last component in " + aContainer);
        synchronized (aContainer.getTreeLock()) {
            if (!(aContainer.isVisible() && aContainer.isDisplayable())) {
                return null;
            }
            for (int i = aContainer.ncomponents - 1; i >= 0; i--) {
                Component comp = aContainer.component[i];
                if (comp instanceof Container && !((Container)(Container)comp).isFocusCycleRoot()) {
                    Component retval = null;
                    Container cont = (Container)(Container)comp;
                    if (cont.isFocusTraversalPolicyProvider()) {
                        if (log.isLoggable(Level.FINE)) log.fine("\tEntering FTP " + cont);
                        FocusTraversalPolicy policy = cont.getFocusTraversalPolicy();
                        retval = policy.getLastComponent(cont);
                    } else {
                        if (log.isLoggable(Level.FINE)) log.fine("\tEntering sub-container");
                        retval = getLastComponent((Container)(Container)comp);
                    }
                    if (retval != null) {
                        if (log.isLoggable(Level.FINE)) log.fine("\tFound last component : " + retval);
                        return retval;
                    }
                } else if (accept(comp)) {
                    return comp;
                }
            }
            if (accept(aContainer)) {
                return aContainer;
            }
        }
        return null;
    }
    
    public Component getDefaultComponent(Container aContainer) {
        return getFirstComponent(aContainer);
    }
    
    public void setImplicitDownCycleTraversal(boolean implicitDownCycleTraversal) {
        this.implicitDownCycleTraversal = implicitDownCycleTraversal;
    }
    
    public boolean getImplicitDownCycleTraversal() {
        return implicitDownCycleTraversal;
    }
    
    protected boolean accept(Component aComponent) {
        if (!(aComponent.isVisible() && aComponent.isDisplayable() && aComponent.isFocusable() && aComponent.isEnabled())) {
            return false;
        }
        if (!(aComponent instanceof Window)) {
            for (Container enableTest = aComponent.getParent(); enableTest != null; enableTest = enableTest.getParent()) {
                if (!(enableTest.isEnabled() || enableTest.isLightweight())) {
                    return false;
                }
                if (enableTest instanceof Window) {
                    break;
                }
            }
        }
        return true;
    }
}
