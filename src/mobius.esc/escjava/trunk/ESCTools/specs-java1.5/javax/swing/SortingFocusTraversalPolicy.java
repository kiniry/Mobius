package javax.swing;

import java.awt.Component;
import java.awt.Container;
import java.util.*;
import java.awt.FocusTraversalPolicy;
import java.util.logging.*;

public class SortingFocusTraversalPolicy extends InternalFrameFocusTraversalPolicy {
    private Comparator comparator;
    private boolean implicitDownCycleTraversal = true;
    private Logger log = Logger.getLogger("javax.swing.SortingFocusTraversalPolicy");
    private Container cachedRoot;
    private List cachedCycle;
    private static final SwingContainerOrderFocusTraversalPolicy fitnessTestPolicy = new SwingContainerOrderFocusTraversalPolicy();
    
    protected SortingFocusTraversalPolicy() {
        
    }
    
    public SortingFocusTraversalPolicy(Comparator comparator) {
        
        this.comparator = comparator;
    }
    
    private void enumerateAndSortCycle(Container focusCycleRoot, List cycle, Map defaults) {
        List defaultRoots = null;
        if (!focusCycleRoot.isShowing()) {
            return;
        }
        enumerateCycle(focusCycleRoot, cycle);
        boolean addDefaultComponents = (defaults != null && getImplicitDownCycleTraversal());
        if (log.isLoggable(Level.FINE)) log.fine("### Will add defaults: " + addDefaultComponents);
        if (addDefaultComponents) {
            defaultRoots = new ArrayList();
            for (Iterator iter = cycle.iterator(); iter.hasNext(); ) {
                Component comp = (Component)(Component)iter.next();
                if ((comp instanceof Container) && ((Container)(Container)comp).isFocusCycleRoot()) {
                    defaultRoots.add(comp);
                }
            }
            Collections.sort(defaultRoots, comparator);
        }
        Collections.sort(cycle, comparator);
        if (addDefaultComponents) {
            for (ListIterator defaultRootsIter = defaultRoots.listIterator(defaultRoots.size()); defaultRootsIter.hasPrevious(); ) {
                Container root = (Container)(Container)defaultRootsIter.previous();
                Component defComp = root.getFocusTraversalPolicy().getDefaultComponent(root);
                if (defComp != null && defComp.isShowing()) {
                    int index = Collections.binarySearch(cycle, root, comparator);
                    if (index < 0) {
                        index = -index - 2;
                    }
                    defaults.put(new Integer(index), defComp);
                }
            }
        }
    }
    
    private void enumerateCycle(Container container, List cycle) {
        if (!(container.isVisible() && container.isDisplayable())) {
            return;
        }
        cycle.add(container);
        Component[] components = container.getComponents();
        for (int i = 0; i < components.length; i++) {
            Component comp = components[i];
            if ((comp instanceof Container) && !((Container)(Container)comp).isFocusTraversalPolicyProvider() && !((Container)(Container)comp).isFocusCycleRoot() && !((comp instanceof JComponent) && ((JComponent)(JComponent)comp).isManagingFocus())) {
                enumerateCycle((Container)(Container)comp, cycle);
            } else {
                cycle.add(comp);
            }
        }
    }
    
    Container getTopmostProvider(Container focusCycleRoot, Component aComponent) {
        Container aCont = aComponent.getParent();
        Container ftp = null;
        while (aCont != focusCycleRoot && aCont != null) {
            if (aCont.isFocusTraversalPolicyProvider()) {
                ftp = aCont;
            }
            aCont = aCont.getParent();
        }
        if (aCont == null) {
            return null;
        }
        return ftp;
    }
    
    public Component getComponentAfter(Container aContainer, Component aComponent) {
        if (log.isLoggable(Level.FINE)) log.fine("### Searching in " + aContainer.getName() + " for component after " + aComponent.getName());
        if (aContainer == null || aComponent == null) {
            throw new IllegalArgumentException("aContainer and aComponent cannot be null");
        }
        if (!aContainer.isFocusTraversalPolicyProvider() && !aContainer.isFocusCycleRoot()) {
            throw new IllegalArgumentException("aContainer should be focus cycle root or focus traversal policy provider");
        } else if (aContainer.isFocusCycleRoot() && !aComponent.isFocusCycleRoot(aContainer)) {
            throw new IllegalArgumentException("aContainer is not a focus cycle root of aComponent");
        }
        Container ftp = getTopmostProvider(aContainer, aComponent);
        if (ftp != null) {
            if (log.isLoggable(Level.FINE)) log.fine("### Asking FTP " + ftp.getName() + " for component after " + aComponent.getName());
            FocusTraversalPolicy policy = ftp.getFocusTraversalPolicy();
            Component retval = policy.getComponentAfter(ftp, aComponent);
            if (retval == policy.getFirstComponent(ftp)) {
                retval = null;
            }
            if (retval != null) {
                if (log.isLoggable(Level.FINE)) log.fine("### FTP returned " + retval.getName());
                return retval;
            }
            aComponent = ftp;
        }
        List cycle = new ArrayList();
        Map defaults = new HashMap();
        enumerateAndSortCycle(aContainer, cycle, defaults);
        int index;
        try {
            index = Collections.binarySearch(cycle, aComponent, comparator);
        } catch (ClassCastException e) {
            if (log.isLoggable(Level.FINE)) log.fine("### Didn\'t find component " + aComponent.getName() + " in a cycle " + aContainer.getName());
            return getFirstComponent(aContainer);
        }
        if (index < 0) {
            int i = cycle.indexOf(aComponent);
            if (i >= 0) {
                index = i;
            } else {
                index = -index - 2;
            }
        }
        Component defComp = (Component)(Component)defaults.get(new Integer(index));
        if (defComp != null) {
            return defComp;
        }
        do {
            index++;
            if (index >= cycle.size()) {
                if (aContainer.isFocusCycleRoot()) {
                    this.cachedRoot = aContainer;
                    this.cachedCycle = cycle;
                    Component retval = getFirstComponent(aContainer);
                    this.cachedRoot = null;
                    this.cachedCycle = null;
                    return retval;
                } else {
                    return null;
                }
            } else {
                Component comp = (Component)(Component)cycle.get(index);
                if (accept(comp)) {
                    return comp;
                } else if (comp instanceof Container && ((Container)(Container)comp).isFocusTraversalPolicyProvider()) {
                    return ((Container)(Container)comp).getFocusTraversalPolicy().getDefaultComponent((Container)(Container)comp);
                }
            }
        }         while (true);
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
        Container ftp = getTopmostProvider(aContainer, aComponent);
        if (ftp != null) {
            if (log.isLoggable(Level.FINE)) log.fine("### Asking FTP " + ftp.getName() + " for component after " + aComponent.getName());
            FocusTraversalPolicy policy = ftp.getFocusTraversalPolicy();
            Component retval = policy.getComponentBefore(ftp, aComponent);
            if (retval == policy.getLastComponent(ftp)) {
                retval = null;
            }
            if (retval != null) {
                if (log.isLoggable(Level.FINE)) log.fine("### FTP returned " + retval.getName());
                return retval;
            }
            aComponent = ftp;
        }
        List cycle = new ArrayList();
        Map defaults = new HashMap();
        enumerateAndSortCycle(aContainer, cycle, defaults);
        if (log.isLoggable(Level.FINE)) log.fine("### Cycle is " + cycle + ", component is " + aComponent);
        int index;
        try {
            index = Collections.binarySearch(cycle, aComponent, comparator);
        } catch (ClassCastException e) {
            return getLastComponent(aContainer);
        }
        if (index < 0) {
            index = -index - 2;
        } else {
            index--;
        }
        if (log.isLoggable(Level.FINE)) log.fine("### Index is " + index);
        if (index >= 0) {
            Component defComp = (Component)(Component)defaults.get(new Integer(index));
            if (defComp != null && cycle.get(index) != aContainer) {
                if (log.isLoggable(Level.FINE)) log.fine("### Returning default " + defComp.getName() + " at " + index);
                return defComp;
            }
        }
        do {
            if (index < 0) {
                this.cachedRoot = aContainer;
                this.cachedCycle = cycle;
                Component retval = getLastComponent(aContainer);
                this.cachedRoot = null;
                this.cachedCycle = null;
                return retval;
            } else {
                Component comp = (Component)(Component)cycle.get(index);
                if (accept(comp)) {
                    return comp;
                } else if (comp instanceof Container && ((Container)(Container)comp).isFocusTraversalPolicyProvider()) {
                    return ((Container)(Container)comp).getFocusTraversalPolicy().getLastComponent((Container)(Container)comp);
                }
            }
            index--;
        }         while (true);
    }
    
    public Component getFirstComponent(Container aContainer) {
        List cycle;
        if (log.isLoggable(Level.FINE)) log.fine("### Getting first component in " + aContainer.getName());
        if (aContainer == null) {
            throw new IllegalArgumentException("aContainer cannot be null");
        }
        if (this.cachedRoot == aContainer) {
            cycle = this.cachedCycle;
        } else {
            cycle = new ArrayList();
            enumerateAndSortCycle(aContainer, cycle, null);
        }
        int size = cycle.size();
        if (size == 0) {
            return null;
        }
        for (int i = 0; i < cycle.size(); i++) {
            Component comp = (Component)(Component)cycle.get(i);
            if (accept(comp)) {
                return comp;
            } else if (comp instanceof Container && !(comp == aContainer) && ((Container)(Container)comp).isFocusTraversalPolicyProvider()) {
                return ((Container)(Container)comp).getFocusTraversalPolicy().getDefaultComponent((Container)(Container)comp);
            }
        }
        return null;
    }
    
    public Component getLastComponent(Container aContainer) {
        List cycle;
        if (log.isLoggable(Level.FINE)) log.fine("### Getting last component in " + aContainer.getName());
        if (aContainer == null) {
            throw new IllegalArgumentException("aContainer cannot be null");
        }
        if (this.cachedRoot == aContainer) {
            cycle = this.cachedCycle;
        } else {
            cycle = new ArrayList();
            enumerateAndSortCycle(aContainer, cycle, null);
        }
        int size = cycle.size();
        if (size == 0) {
            if (log.isLoggable(Level.FINE)) log.fine("### Cycle is empty");
            return null;
        }
        if (log.isLoggable(Level.FINE)) log.fine("### Cycle is " + cycle);
        for (int i = cycle.size() - 1; i >= 0; i--) {
            Component comp = (Component)(Component)cycle.get(i);
            if (accept(comp)) {
                return comp;
            } else if (comp instanceof Container && !(comp == aContainer) && ((Container)(Container)comp).isFocusTraversalPolicyProvider()) {
                return ((Container)(Container)comp).getFocusTraversalPolicy().getLastComponent((Container)(Container)comp);
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
    
    protected void setComparator(Comparator comparator) {
        this.comparator = comparator;
    }
    
    protected Comparator getComparator() {
        return comparator;
    }
    
    protected boolean accept(Component aComponent) {
        return fitnessTestPolicy.accept(aComponent);
    }
}
