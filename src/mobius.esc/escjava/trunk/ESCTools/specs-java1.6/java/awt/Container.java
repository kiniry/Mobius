package java.awt;

import java.io.PrintStream;
import java.io.PrintWriter;
import java.awt.peer.ContainerPeer;
import java.awt.peer.LightweightPeer;
import sun.awt.PeerEvent;
import java.awt.event.ComponentEvent;
import java.awt.event.ContainerEvent;
import java.awt.event.HierarchyEvent;
import java.awt.event.KeyEvent;
import java.awt.event.ContainerListener;
import java.util.EventListener;
import java.io.ObjectStreamField;
import java.io.ObjectOutputStream;
import java.io.ObjectInputStream;
import java.io.IOException;
import java.util.HashSet;
import java.util.Set;
import javax.accessibility.*;
import java.beans.PropertyChangeListener;
import sun.awt.AppContext;
import sun.awt.DebugHelper;
import sun.awt.SunToolkit;

public class Container extends Component {
    /*synthetic*/ static final boolean $assertionsDisabled = !Container.class.desiredAssertionStatus();
    int ncomponents;
    Component[] component = new Component[0];
    LayoutManager layoutMgr;
    private LightweightDispatcher dispatcher;
    private transient FocusTraversalPolicy focusTraversalPolicy;
    private boolean focusCycleRoot = false;
    private boolean focusTraversalPolicyProvider;
    private transient Set printingThreads;
    private transient boolean printing = false;
    transient ContainerListener containerListener;
    transient int listeningChildren;
    transient int listeningBoundsChildren;
    transient int descendantsCount;
    private static final long serialVersionUID = 4613797578919906343L;
    private static final DebugHelper dbg = DebugHelper.create(Container.class);
    static final boolean INCLUDE_SELF = true;
    static final boolean SEARCH_HEAVYWEIGHTS = true;
    private static final ObjectStreamField[] serialPersistentFields = {new ObjectStreamField("ncomponents", Integer.TYPE), new ObjectStreamField("component", Component[].class), new ObjectStreamField("layoutMgr", LayoutManager.class), new ObjectStreamField("dispatcher", LightweightDispatcher.class), new ObjectStreamField("maxSize", Dimension.class), new ObjectStreamField("focusCycleRoot", Boolean.TYPE), new ObjectStreamField("containerSerializedDataVersion", Integer.TYPE), new ObjectStreamField("focusTraversalPolicyProvider", Boolean.TYPE)};
    static {
        Toolkit.loadLibraries();
        if (!GraphicsEnvironment.isHeadless()) {
            initIDs();
        }
    }
    
    private static native void initIDs();
    
    public Container() {
        
    }
    
    void initializeFocusTraversalKeys() {
        focusTraversalKeys = new Set[4];
    }
    
    public int getComponentCount() {
        return countComponents();
    }
    
    
    public int countComponents() {
        return ncomponents;
    }
    
    public Component getComponent(int n) {
        synchronized (getTreeLock()) {
            if ((n < 0) || (n >= ncomponents)) {
                throw new ArrayIndexOutOfBoundsException("No such child: " + n);
            }
            return component[n];
        }
    }
    
    public Component[] getComponents() {
        return getComponents_NoClientCode();
    }
    
    final Component[] getComponents_NoClientCode() {
        synchronized (getTreeLock()) {
            Component[] list = new Component[ncomponents];
            System.arraycopy(component, 0, list, 0, ncomponents);
            return list;
        }
    }
    
    public Insets getInsets() {
        return insets();
    }
    
    
    public Insets insets() {
        if (this.peer != null && this.peer instanceof ContainerPeer) {
            ContainerPeer peer = (ContainerPeer)(ContainerPeer)this.peer;
            return (Insets)(Insets)peer.insets().clone();
        }
        return new Insets(0, 0, 0, 0);
    }
    
    public Component add(Component comp) {
        addImpl(comp, null, -1);
        return comp;
    }
    
    public Component add(String name, Component comp) {
        addImpl(comp, name, -1);
        return comp;
    }
    
    public Component add(Component comp, int index) {
        addImpl(comp, null, index);
        return comp;
    }
    
    void checkTreeLock() {
        if (!Thread.holdsLock(getTreeLock())) {
            throw new IllegalStateException("This function should be called while holding treeLock");
        }
    }
    
    private void checkAdding(Component comp, int index) {
        checkTreeLock();
        GraphicsConfiguration thisGC = getGraphicsConfiguration();
        if (index > ncomponents || index < 0) {
            throw new IllegalArgumentException("illegal component position");
        }
        if (comp.parent == this) {
            if (index == ncomponents) {
                throw new IllegalArgumentException("illegal component position " + index + " should be less then " + ncomponents);
            }
        }
        if (comp instanceof Container) {
            for (Container cn = this; cn != null; cn = cn.parent) {
                if (cn == comp) {
                    throw new IllegalArgumentException("adding container\'s parent to itself");
                }
            }
            if (comp instanceof Window) {
                throw new IllegalArgumentException("adding a window to a container");
            }
        }
        Window thisTopLevel = getContainingWindow();
        Window compTopLevel = comp.getContainingWindow();
        if (thisTopLevel != compTopLevel) {
            throw new IllegalArgumentException("component and container should be in the same top-level window");
        }
        if (thisGC != null) {
            comp.checkGD(thisGC.getDevice().getIDstring());
        }
    }
    
    private void removeDelicately(Component comp, Container newParent, int newIndex) {
        checkTreeLock();
        int index = getComponentZOrder(comp);
        if (isRemoveNotifyNeeded(comp, this, newParent)) {
            comp.removeNotify();
        }
        if (newParent != this) {
            if (layoutMgr != null) {
                layoutMgr.removeLayoutComponent(comp);
            }
            adjustListeningChildren(AWTEvent.HIERARCHY_EVENT_MASK, -comp.numListening(AWTEvent.HIERARCHY_EVENT_MASK));
            adjustListeningChildren(AWTEvent.HIERARCHY_BOUNDS_EVENT_MASK, -comp.numListening(AWTEvent.HIERARCHY_BOUNDS_EVENT_MASK));
            adjustDescendants(-(comp.countHierarchyMembers()));
            comp.parent = null;
            System.arraycopy(component, index + 1, component, index, ncomponents - index - 1);
            component[--ncomponents] = null;
            if (valid) {
                invalidate();
            }
        } else {
            if (newIndex > index) {
                if (newIndex - index > 0) {
                    System.arraycopy(component, index + 1, component, index, newIndex - index);
                }
            } else {
                if (index - newIndex > 0) {
                    System.arraycopy(component, newIndex, component, newIndex + 1, index - newIndex);
                }
            }
            component[newIndex] = comp;
        }
        if (comp.parent == null) {
            if (containerListener != null || (eventMask & AWTEvent.CONTAINER_EVENT_MASK) != 0 || Toolkit.enabledOnToolkit(AWTEvent.CONTAINER_EVENT_MASK)) {
                ContainerEvent e = new ContainerEvent(this, ContainerEvent.COMPONENT_REMOVED, comp);
                dispatchEvent(e);
            }
            comp.createHierarchyEvents(HierarchyEvent.HIERARCHY_CHANGED, comp, this, HierarchyEvent.PARENT_CHANGED, Toolkit.enabledOnToolkit(AWTEvent.HIERARCHY_EVENT_MASK));
            if (peer != null && layoutMgr == null && isVisible()) {
                updateCursorImmediately();
            }
        }
    }
    
    boolean canContainFocusOwner(Component focusOwnerCandidate) {
        if (!(isEnabled() && isDisplayable() && isVisible() && isFocusable())) {
            return false;
        }
        if (isFocusCycleRoot()) {
            FocusTraversalPolicy policy = getFocusTraversalPolicy();
            if (policy instanceof DefaultFocusTraversalPolicy) {
                if (!((DefaultFocusTraversalPolicy)(DefaultFocusTraversalPolicy)policy).accept(focusOwnerCandidate)) {
                    return false;
                }
            }
        }
        synchronized (getTreeLock()) {
            if (parent != null) {
                return parent.canContainFocusOwner(focusOwnerCandidate);
            }
        }
        return true;
    }
    
    private boolean hasHeavyweightChildren() {
        checkTreeLock();
        boolean res = true;
        for (int i = 0; i < getComponentCount() && res; i++) {
            Component child = getComponent(i);
            res &= child.isLightweight();
            if (res && child instanceof Container) {
                res &= !((Container)(Container)child).hasHeavyweightChildren();
            }
        }
        return !res;
    }
    
    Container getHeavyweightContainer() {
        checkTreeLock();
        if (peer != null && !(peer instanceof LightweightPeer)) {
            return this;
        } else {
            return getNativeContainer();
        }
    }
    
    private static boolean isRemoveNotifyNeeded(Component comp, Container oldContainer, Container newContainer) {
        if (oldContainer == null) {
            return false;
        }
        if (comp.peer == null) {
            return false;
        }
        if (newContainer.peer == null) {
            return true;
        }
        if (comp.isLightweight()) {
            if (comp instanceof Container) {
                return ((Container)(Container)comp).hasHeavyweightChildren();
            } else {
                return false;
            }
        }
        Container newNativeContainer = oldContainer.getHeavyweightContainer();
        Container oldNativeContainer = newContainer.getHeavyweightContainer();
        if (newNativeContainer != oldNativeContainer) {
            return !comp.peer.isReparentSupported();
        } else {
            return !comp.isLightweight() && !((ContainerPeer)((ContainerPeer)newNativeContainer.peer)).isRestackSupported();
        }
    }
    
    public final void setComponentZOrder(Component comp, int index) {
        synchronized (getTreeLock()) {
            Container curParent = comp.parent;
            if (curParent == this && index == getComponentZOrder(comp)) {
                return;
            }
            checkAdding(comp, index);
            if (curParent != null) {
                curParent.removeDelicately(comp, this, index);
            }
            addDelicately(comp, curParent, index);
        }
    }
    
    private void reparentTraverse(ContainerPeer parentPeer, Container child) {
        checkTreeLock();
        for (int i = 0; i < child.getComponentCount(); i++) {
            Component comp = child.getComponent(i);
            if (comp.isLightweight()) {
                if (comp instanceof Container) {
                    reparentTraverse(parentPeer, (Container)(Container)comp);
                }
            } else {
                comp.getPeer().reparent(parentPeer);
            }
        }
    }
    
    private void reparentChild(Component comp) {
        checkTreeLock();
        if (comp == null) {
            return;
        }
        if (comp.isLightweight()) {
            if (comp instanceof Container) {
                reparentTraverse((ContainerPeer)(ContainerPeer)getPeer(), (Container)(Container)comp);
            }
        } else {
            comp.getPeer().reparent((ContainerPeer)(ContainerPeer)getPeer());
        }
    }
    
    private void addDelicately(Component comp, Container curParent, int index) {
        checkTreeLock();
        if (curParent != this) {
            if (ncomponents == component.length) {
                Component[] newcomponents = new Component[ncomponents * 2 + 1];
                System.arraycopy(component, 0, newcomponents, 0, ncomponents);
                component = newcomponents;
            }
            if (index == -1 || index == ncomponents) {
                component[ncomponents++] = comp;
            } else {
                System.arraycopy(component, index, component, index + 1, ncomponents - index);
                component[index] = comp;
                ncomponents++;
            }
            comp.parent = this;
            adjustListeningChildren(AWTEvent.HIERARCHY_EVENT_MASK, comp.numListening(AWTEvent.HIERARCHY_EVENT_MASK));
            adjustListeningChildren(AWTEvent.HIERARCHY_BOUNDS_EVENT_MASK, comp.numListening(AWTEvent.HIERARCHY_BOUNDS_EVENT_MASK));
            adjustDescendants(comp.countHierarchyMembers());
        } else {
            if (index < ncomponents) {
                component[index] = comp;
            }
        }
        if (valid) {
            invalidate();
        }
        if (peer != null) {
            if (comp.peer == null) {
                comp.addNotify();
                Container newNativeContainer = getHeavyweightContainer();
                if (((ContainerPeer)(ContainerPeer)newNativeContainer.getPeer()).isRestackSupported()) {
                    ((ContainerPeer)(ContainerPeer)newNativeContainer.getPeer()).restack();
                }
            } else {
                Container newNativeContainer = getHeavyweightContainer();
                Container oldNativeContainer = curParent.getHeavyweightContainer();
                if (oldNativeContainer != newNativeContainer) {
                    newNativeContainer.reparentChild(comp);
                }
                if ((!comp.isLightweight() || (comp instanceof Container)) && ((ContainerPeer)(ContainerPeer)newNativeContainer.getPeer()).isRestackSupported()) {
                    ((ContainerPeer)(ContainerPeer)newNativeContainer.getPeer()).restack();
                }
                if (!comp.isLightweight() && isLightweight()) {
                    if (!curParent.isLightweight()) {
                        comp.nativeInLightFixer = new Component$NativeInLightFixer(this);
                    } else {
                        comp.nativeInLightFixer.install(this);
                    }
                }
            }
        }
        if (curParent != this) {
            if (layoutMgr != null) {
                if (layoutMgr instanceof LayoutManager2) {
                    ((LayoutManager2)(LayoutManager2)layoutMgr).addLayoutComponent(comp, null);
                } else {
                    layoutMgr.addLayoutComponent(null, comp);
                }
            }
            if (containerListener != null || (eventMask & AWTEvent.CONTAINER_EVENT_MASK) != 0 || Toolkit.enabledOnToolkit(AWTEvent.CONTAINER_EVENT_MASK)) {
                ContainerEvent e = new ContainerEvent(this, ContainerEvent.COMPONENT_ADDED, comp);
                dispatchEvent(e);
            }
            comp.createHierarchyEvents(HierarchyEvent.HIERARCHY_CHANGED, comp, this, HierarchyEvent.PARENT_CHANGED, Toolkit.enabledOnToolkit(AWTEvent.HIERARCHY_EVENT_MASK));
            if (comp.isFocusOwner() && !comp.canBeFocusOwner()) {
                comp.transferFocus();
            } else if (comp instanceof Container) {
                Component focusOwner = KeyboardFocusManager.getCurrentKeyboardFocusManager().getFocusOwner();
                if (focusOwner != null && isParentOf(focusOwner) && !focusOwner.canBeFocusOwner()) {
                    focusOwner.transferFocus();
                }
            }
        } else {
            comp.createHierarchyEvents(HierarchyEvent.HIERARCHY_CHANGED, comp, this, HierarchyEvent.HIERARCHY_CHANGED, Toolkit.enabledOnToolkit(AWTEvent.HIERARCHY_EVENT_MASK));
        }
        if (peer != null && layoutMgr == null && isVisible()) {
            updateCursorImmediately();
        }
    }
    
    public final int getComponentZOrder(Component comp) {
        if (comp == null) {
            return -1;
        }
        synchronized (getTreeLock()) {
            if (comp.parent != this) {
                return -1;
            }
            for (int i = 0; i < ncomponents; i++) {
                if (component[i] == comp) {
                    return i;
                }
            }
        }
        return -1;
    }
    
    public void add(Component comp, Object constraints) {
        addImpl(comp, constraints, -1);
    }
    
    public void add(Component comp, Object constraints, int index) {
        addImpl(comp, constraints, index);
    }
    
    protected void addImpl(Component comp, Object constraints, int index) {
        synchronized (getTreeLock()) {
            GraphicsConfiguration thisGC = this.getGraphicsConfiguration();
            if (index > ncomponents || (index < 0 && index != -1)) {
                throw new IllegalArgumentException("illegal component position");
            }
            if (comp instanceof Container) {
                for (Container cn = this; cn != null; cn = cn.parent) {
                    if (cn == comp) {
                        throw new IllegalArgumentException("adding container\'s parent to itself");
                    }
                }
                if (comp instanceof Window) {
                    throw new IllegalArgumentException("adding a window to a container");
                }
            }
            if (thisGC != null) {
                comp.checkGD(thisGC.getDevice().getIDstring());
            }
            if (comp.parent != null) {
                comp.parent.remove(comp);
                if (index > ncomponents) {
                    throw new IllegalArgumentException("illegal component position");
                }
            }
            if (ncomponents == component.length) {
                Component[] newcomponents = new Component[ncomponents * 2 + 1];
                System.arraycopy(component, 0, newcomponents, 0, ncomponents);
                component = newcomponents;
            }
            if (index == -1 || index == ncomponents) {
                component[ncomponents++] = comp;
            } else {
                System.arraycopy(component, index, component, index + 1, ncomponents - index);
                component[index] = comp;
                ncomponents++;
            }
            comp.parent = this;
            adjustListeningChildren(AWTEvent.HIERARCHY_EVENT_MASK, comp.numListening(AWTEvent.HIERARCHY_EVENT_MASK));
            adjustListeningChildren(AWTEvent.HIERARCHY_BOUNDS_EVENT_MASK, comp.numListening(AWTEvent.HIERARCHY_BOUNDS_EVENT_MASK));
            adjustDescendants(comp.countHierarchyMembers());
            if (valid) {
                invalidate();
            }
            if (peer != null) {
                comp.addNotify();
            }
            if (layoutMgr != null) {
                if (layoutMgr instanceof LayoutManager2) {
                    ((LayoutManager2)(LayoutManager2)layoutMgr).addLayoutComponent(comp, constraints);
                } else if (constraints instanceof String) {
                    layoutMgr.addLayoutComponent((String)(String)constraints, comp);
                }
            }
            if (containerListener != null || (eventMask & AWTEvent.CONTAINER_EVENT_MASK) != 0 || Toolkit.enabledOnToolkit(AWTEvent.CONTAINER_EVENT_MASK)) {
                ContainerEvent e = new ContainerEvent(this, ContainerEvent.COMPONENT_ADDED, comp);
                dispatchEvent(e);
            }
            comp.createHierarchyEvents(HierarchyEvent.HIERARCHY_CHANGED, comp, this, HierarchyEvent.PARENT_CHANGED, Toolkit.enabledOnToolkit(AWTEvent.HIERARCHY_EVENT_MASK));
            if (peer != null && layoutMgr == null && isVisible()) {
                updateCursorImmediately();
            }
        }
    }
    
    void checkGD(String stringID) {
        Component tempComp;
        for (int i = 0; i < component.length; i++) {
            tempComp = component[i];
            if (tempComp != null) {
                tempComp.checkGD(stringID);
            }
        }
    }
    
    public void remove(int index) {
        synchronized (getTreeLock()) {
            if (index < 0 || index >= ncomponents) {
                throw new ArrayIndexOutOfBoundsException(index);
            }
            Component comp = component[index];
            if (peer != null) {
                comp.removeNotify();
            }
            if (layoutMgr != null) {
                layoutMgr.removeLayoutComponent(comp);
            }
            adjustListeningChildren(AWTEvent.HIERARCHY_EVENT_MASK, -comp.numListening(AWTEvent.HIERARCHY_EVENT_MASK));
            adjustListeningChildren(AWTEvent.HIERARCHY_BOUNDS_EVENT_MASK, -comp.numListening(AWTEvent.HIERARCHY_BOUNDS_EVENT_MASK));
            adjustDescendants(-(comp.countHierarchyMembers()));
            comp.parent = null;
            System.arraycopy(component, index + 1, component, index, ncomponents - index - 1);
            component[--ncomponents] = null;
            if (valid) {
                invalidate();
            }
            if (containerListener != null || (eventMask & AWTEvent.CONTAINER_EVENT_MASK) != 0 || Toolkit.enabledOnToolkit(AWTEvent.CONTAINER_EVENT_MASK)) {
                ContainerEvent e = new ContainerEvent(this, ContainerEvent.COMPONENT_REMOVED, comp);
                dispatchEvent(e);
            }
            comp.createHierarchyEvents(HierarchyEvent.HIERARCHY_CHANGED, comp, this, HierarchyEvent.PARENT_CHANGED, Toolkit.enabledOnToolkit(AWTEvent.HIERARCHY_EVENT_MASK));
            if (peer != null && layoutMgr == null && isVisible()) {
                updateCursorImmediately();
            }
        }
    }
    
    public void remove(Component comp) {
        synchronized (getTreeLock()) {
            if (comp.parent == this) {
                Component[] component = this.component;
                for (int i = ncomponents; --i >= 0; ) {
                    if (component[i] == comp) {
                        remove(i);
                    }
                }
            }
        }
    }
    
    public void removeAll() {
        synchronized (getTreeLock()) {
            adjustListeningChildren(AWTEvent.HIERARCHY_EVENT_MASK, -listeningChildren);
            adjustListeningChildren(AWTEvent.HIERARCHY_BOUNDS_EVENT_MASK, -listeningBoundsChildren);
            adjustDescendants(-descendantsCount);
            while (ncomponents > 0) {
                Component comp = component[--ncomponents];
                component[ncomponents] = null;
                if (peer != null) {
                    comp.removeNotify();
                }
                if (layoutMgr != null) {
                    layoutMgr.removeLayoutComponent(comp);
                }
                comp.parent = null;
                if (containerListener != null || (eventMask & AWTEvent.CONTAINER_EVENT_MASK) != 0 || Toolkit.enabledOnToolkit(AWTEvent.CONTAINER_EVENT_MASK)) {
                    ContainerEvent e = new ContainerEvent(this, ContainerEvent.COMPONENT_REMOVED, comp);
                    dispatchEvent(e);
                }
                comp.createHierarchyEvents(HierarchyEvent.HIERARCHY_CHANGED, comp, this, HierarchyEvent.PARENT_CHANGED, Toolkit.enabledOnToolkit(AWTEvent.HIERARCHY_EVENT_MASK));
            }
            if (peer != null && layoutMgr == null && isVisible()) {
                updateCursorImmediately();
            }
            if (valid) {
                invalidate();
            }
        }
    }
    
    int numListening(long mask) {
        int superListening = super.numListening(mask);
        if (mask == AWTEvent.HIERARCHY_EVENT_MASK) {
            if (dbg.on) {
                int sum = 0;
                for (int i = 0; i < ncomponents; i++) {
                    sum += component[i].numListening(mask);
                }
                dbg.assertion(listeningChildren == sum);
            }
            return listeningChildren + superListening;
        } else if (mask == AWTEvent.HIERARCHY_BOUNDS_EVENT_MASK) {
            if (dbg.on) {
                int sum = 0;
                for (int i = 0; i < ncomponents; i++) {
                    sum += component[i].numListening(mask);
                }
                dbg.assertion(listeningBoundsChildren == sum);
            }
            return listeningBoundsChildren + superListening;
        } else {
            if (dbg.on) {
                dbg.assertion(false);
            }
            return superListening;
        }
    }
    
    void adjustListeningChildren(long mask, int num) {
        if (dbg.on) {
            dbg.assertion(mask == AWTEvent.HIERARCHY_EVENT_MASK || mask == AWTEvent.HIERARCHY_BOUNDS_EVENT_MASK || mask == (AWTEvent.HIERARCHY_EVENT_MASK | AWTEvent.HIERARCHY_BOUNDS_EVENT_MASK));
        }
        if (num == 0) return;
        if ((mask & AWTEvent.HIERARCHY_EVENT_MASK) != 0) {
            listeningChildren += num;
        }
        if ((mask & AWTEvent.HIERARCHY_BOUNDS_EVENT_MASK) != 0) {
            listeningBoundsChildren += num;
        }
        adjustListeningChildrenOnParent(mask, num);
    }
    
    void adjustDescendants(int num) {
        if (num == 0) return;
        descendantsCount += num;
        adjustDecendantsOnParent(num);
    }
    
    void adjustDecendantsOnParent(int num) {
        if (parent != null) {
            parent.adjustDescendants(num);
        }
    }
    
    int countHierarchyMembers() {
        if (dbg.on) {
            int sum = 0;
            for (int i = 0; i < ncomponents; i++) {
                sum += component[i].countHierarchyMembers();
            }
            dbg.assertion(descendantsCount == sum);
        }
        return descendantsCount + 1;
    }
    
    private int getListenersCount(int id, boolean enabledOnToolkit) {
        if (!$assertionsDisabled && !Thread.holdsLock(getTreeLock())) throw new AssertionError();
        if (enabledOnToolkit) {
            return descendantsCount;
        }
        switch (id) {
        case HierarchyEvent.HIERARCHY_CHANGED: 
            return listeningChildren;
        
        case HierarchyEvent.ANCESTOR_MOVED: 
        
        case HierarchyEvent.ANCESTOR_RESIZED: 
            return listeningBoundsChildren;
        
        default: 
            return 0;
        
        }
    }
    
    final int createHierarchyEvents(int id, Component changed, Container changedParent, long changeFlags, boolean enabledOnToolkit) {
        if (!$assertionsDisabled && !Thread.holdsLock(getTreeLock())) throw new AssertionError();
        int listeners = getListenersCount(id, enabledOnToolkit);
        for (int count = listeners, i = 0; count > 0; i++) {
            count -= component[i].createHierarchyEvents(id, changed, changedParent, changeFlags, enabledOnToolkit);
        }
        return listeners + super.createHierarchyEvents(id, changed, changedParent, changeFlags, enabledOnToolkit);
    }
    
    final void createChildHierarchyEvents(int id, long changeFlags, boolean enabledOnToolkit) {
        if (!$assertionsDisabled && !Thread.holdsLock(getTreeLock())) throw new AssertionError();
        if (ncomponents == 0) {
            return;
        }
        int listeners = getListenersCount(id, enabledOnToolkit);
        for (int count = listeners, i = 0; count > 0; i++) {
            count -= component[i].createHierarchyEvents(id, this, parent, changeFlags, enabledOnToolkit);
        }
    }
    
    public LayoutManager getLayout() {
        return layoutMgr;
    }
    
    public void setLayout(LayoutManager mgr) {
        layoutMgr = mgr;
        if (valid) {
            invalidate();
        }
    }
    
    public void doLayout() {
        layout();
    }
    
    
    public void layout() {
        LayoutManager layoutMgr = this.layoutMgr;
        if (layoutMgr != null) {
            layoutMgr.layoutContainer(this);
        }
    }
    
    public void invalidate() {
        LayoutManager layoutMgr = this.layoutMgr;
        if (layoutMgr instanceof LayoutManager2) {
            LayoutManager2 lm = (LayoutManager2)(LayoutManager2)layoutMgr;
            lm.invalidateLayout(this);
        }
        super.invalidate();
    }
    
    public void validate() {
        if (!valid) {
            boolean updateCur = false;
            synchronized (getTreeLock()) {
                if (!valid && peer != null) {
                    ContainerPeer p = null;
                    if (peer instanceof ContainerPeer) {
                        p = (ContainerPeer)(ContainerPeer)peer;
                    }
                    if (p != null) {
                        p.beginValidate();
                    }
                    validateTree();
                    valid = true;
                    if (p != null) {
                        p.endValidate();
                        updateCur = isVisible();
                    }
                }
            }
            if (updateCur) {
                updateCursorImmediately();
            }
        }
    }
    
    protected void validateTree() {
        if (!valid) {
            if (peer instanceof ContainerPeer) {
                ((ContainerPeer)(ContainerPeer)peer).beginLayout();
            }
            doLayout();
            Component[] component = this.component;
            for (int i = 0; i < ncomponents; ++i) {
                Component comp = component[i];
                if ((comp instanceof Container) && !(comp instanceof Window) && !comp.valid) {
                    ((Container)(Container)comp).validateTree();
                } else {
                    comp.validate();
                }
            }
            if (peer instanceof ContainerPeer) {
                ((ContainerPeer)(ContainerPeer)peer).endLayout();
            }
        }
        valid = true;
    }
    
    void invalidateTree() {
        synchronized (getTreeLock()) {
            for (int i = 0; i < ncomponents; ++i) {
                Component comp = component[i];
                if (comp instanceof Container) {
                    ((Container)(Container)comp).invalidateTree();
                } else {
                    if (comp.valid) {
                        comp.invalidate();
                    }
                }
            }
            if (valid) {
                invalidate();
            }
        }
    }
    
    public void setFont(Font f) {
        boolean shouldinvalidate = false;
        Font oldfont = getFont();
        super.setFont(f);
        Font newfont = getFont();
        if (newfont != oldfont && (oldfont == null || !oldfont.equals(newfont))) {
            invalidateTree();
        }
    }
    
    public Dimension getPreferredSize() {
        return preferredSize();
    }
    
    
    public Dimension preferredSize() {
        Dimension dim = prefSize;
        if (dim == null || !(isPreferredSizeSet() || isValid())) {
            synchronized (getTreeLock()) {
                prefSize = (layoutMgr != null) ? layoutMgr.preferredLayoutSize(this) : super.preferredSize();
                dim = prefSize;
            }
        }
        if (dim != null) {
            return new Dimension(dim);
        } else {
            return dim;
        }
    }
    
    public Dimension getMinimumSize() {
        return minimumSize();
    }
    
    
    public Dimension minimumSize() {
        Dimension dim = minSize;
        if (dim == null || !(isMinimumSizeSet() || isValid())) {
            synchronized (getTreeLock()) {
                minSize = (layoutMgr != null) ? layoutMgr.minimumLayoutSize(this) : super.minimumSize();
                dim = minSize;
            }
        }
        if (dim != null) {
            return new Dimension(dim);
        } else {
            return dim;
        }
    }
    
    public Dimension getMaximumSize() {
        Dimension dim = maxSize;
        if (dim == null || !(isMaximumSizeSet() || isValid())) {
            synchronized (getTreeLock()) {
                if (layoutMgr instanceof LayoutManager2) {
                    LayoutManager2 lm = (LayoutManager2)(LayoutManager2)layoutMgr;
                    maxSize = lm.maximumLayoutSize(this);
                } else {
                    maxSize = super.getMaximumSize();
                }
                dim = maxSize;
            }
        }
        if (dim != null) {
            return new Dimension(dim);
        } else {
            return dim;
        }
    }
    
    public float getAlignmentX() {
        float xAlign;
        if (layoutMgr instanceof LayoutManager2) {
            synchronized (getTreeLock()) {
                LayoutManager2 lm = (LayoutManager2)(LayoutManager2)layoutMgr;
                xAlign = lm.getLayoutAlignmentX(this);
            }
        } else {
            xAlign = super.getAlignmentX();
        }
        return xAlign;
    }
    
    public float getAlignmentY() {
        float yAlign;
        if (layoutMgr instanceof LayoutManager2) {
            synchronized (getTreeLock()) {
                LayoutManager2 lm = (LayoutManager2)(LayoutManager2)layoutMgr;
                yAlign = lm.getLayoutAlignmentY(this);
            }
        } else {
            yAlign = super.getAlignmentY();
        }
        return yAlign;
    }
    
    public void paint(Graphics g) {
        if (isShowing()) {
            if (printing) {
                synchronized (this) {
                    if (printing) {
                        if (printingThreads.contains(Thread.currentThread())) {
                            return;
                        }
                    }
                }
            }
            GraphicsCallback$PaintCallback.getInstance().runComponents(component, g, GraphicsCallback.LIGHTWEIGHTS);
        }
    }
    
    public void update(Graphics g) {
        if (isShowing()) {
            if (!(peer instanceof LightweightPeer)) {
                g.clearRect(0, 0, width, height);
            }
            paint(g);
        }
    }
    
    public void print(Graphics g) {
        if (isShowing()) {
            Thread t = Thread.currentThread();
            try {
                synchronized (this) {
                    if (printingThreads == null) {
                        printingThreads = new HashSet();
                    }
                    printingThreads.add(t);
                    printing = true;
                }
                super.print(g);
            } finally {
                synchronized (this) {
                    printingThreads.remove(t);
                    printing = !printingThreads.isEmpty();
                }
            }
            GraphicsCallback$PrintCallback.getInstance().runComponents(component, g, GraphicsCallback.LIGHTWEIGHTS);
        }
    }
    
    public void paintComponents(Graphics g) {
        if (isShowing()) {
            GraphicsCallback$PaintAllCallback.getInstance().runComponents(component, g, GraphicsCallback.TWO_PASSES);
        }
    }
    
    void lightweightPaint(Graphics g) {
        super.lightweightPaint(g);
        paintHeavyweightComponents(g);
    }
    
    void paintHeavyweightComponents(Graphics g) {
        if (isShowing()) {
            GraphicsCallback$PaintHeavyweightComponentsCallback.getInstance().runComponents(component, g, GraphicsCallback.LIGHTWEIGHTS | GraphicsCallback.HEAVYWEIGHTS);
        }
    }
    
    public void printComponents(Graphics g) {
        if (isShowing()) {
            GraphicsCallback$PrintAllCallback.getInstance().runComponents(component, g, GraphicsCallback.TWO_PASSES);
        }
    }
    
    void lightweightPrint(Graphics g) {
        super.lightweightPrint(g);
        printHeavyweightComponents(g);
    }
    
    void printHeavyweightComponents(Graphics g) {
        if (isShowing()) {
            GraphicsCallback$PrintHeavyweightComponentsCallback.getInstance().runComponents(component, g, GraphicsCallback.LIGHTWEIGHTS | GraphicsCallback.HEAVYWEIGHTS);
        }
    }
    
    public synchronized void addContainerListener(ContainerListener l) {
        if (l == null) {
            return;
        }
        containerListener = AWTEventMulticaster.add(containerListener, l);
        newEventsOnly = true;
    }
    
    public synchronized void removeContainerListener(ContainerListener l) {
        if (l == null) {
            return;
        }
        containerListener = AWTEventMulticaster.remove(containerListener, l);
    }
    
    public synchronized ContainerListener[] getContainerListeners() {
        return (ContainerListener[])((ContainerListener[])getListeners(ContainerListener.class));
    }
    
    public EventListener[] getListeners(Class listenerType) {
        EventListener l = null;
        if (listenerType == ContainerListener.class) {
            l = containerListener;
        } else {
            return super.getListeners(listenerType);
        }
        return AWTEventMulticaster.getListeners(l, listenerType);
    }
    
    boolean eventEnabled(AWTEvent e) {
        int id = e.getID();
        if (id == ContainerEvent.COMPONENT_ADDED || id == ContainerEvent.COMPONENT_REMOVED) {
            if ((eventMask & AWTEvent.CONTAINER_EVENT_MASK) != 0 || containerListener != null) {
                return true;
            }
            return false;
        }
        return super.eventEnabled(e);
    }
    
    protected void processEvent(AWTEvent e) {
        if (e instanceof ContainerEvent) {
            processContainerEvent((ContainerEvent)(ContainerEvent)e);
            return;
        }
        super.processEvent(e);
    }
    
    protected void processContainerEvent(ContainerEvent e) {
        ContainerListener listener = containerListener;
        if (listener != null) {
            switch (e.getID()) {
            case ContainerEvent.COMPONENT_ADDED: 
                listener.componentAdded(e);
                break;
            
            case ContainerEvent.COMPONENT_REMOVED: 
                listener.componentRemoved(e);
                break;
            
            }
        }
    }
    
    void dispatchEventImpl(AWTEvent e) {
        if ((dispatcher != null) && dispatcher.dispatchEvent(e)) {
            e.consume();
            if (peer != null) {
                peer.handleEvent(e);
            }
            return;
        }
        super.dispatchEventImpl(e);
        synchronized (getTreeLock()) {
            switch (e.getID()) {
            case ComponentEvent.COMPONENT_RESIZED: 
                createChildHierarchyEvents(HierarchyEvent.ANCESTOR_RESIZED, 0, Toolkit.enabledOnToolkit(AWTEvent.HIERARCHY_BOUNDS_EVENT_MASK));
                break;
            
            case ComponentEvent.COMPONENT_MOVED: 
                createChildHierarchyEvents(HierarchyEvent.ANCESTOR_MOVED, 0, Toolkit.enabledOnToolkit(AWTEvent.HIERARCHY_BOUNDS_EVENT_MASK));
                break;
            
            default: 
                break;
            
            }
        }
    }
    
    void dispatchEventToSelf(AWTEvent e) {
        super.dispatchEventImpl(e);
    }
    
    Component getMouseEventTarget(int x, int y, boolean includeSelf) {
        return getMouseEventTarget(x, y, includeSelf, Container$MouseEventTargetFilter.FILTER, !SEARCH_HEAVYWEIGHTS);
    }
    
    Component getDropTargetEventTarget(int x, int y, boolean includeSelf) {
        return getMouseEventTarget(x, y, includeSelf, Container$DropTargetEventTargetFilter.FILTER, SEARCH_HEAVYWEIGHTS);
    }
    
    private Component getMouseEventTarget(int x, int y, boolean includeSelf, Container$EventTargetFilter filter, boolean searchHeavyweights) {
        Component comp = null;
        if (searchHeavyweights) {
            comp = getMouseEventTargetImpl(x, y, includeSelf, filter, SEARCH_HEAVYWEIGHTS, searchHeavyweights);
        }
        if (comp == null || comp == this) {
            comp = getMouseEventTargetImpl(x, y, includeSelf, filter, !SEARCH_HEAVYWEIGHTS, searchHeavyweights);
        }
        return comp;
    }
    
    private Component getMouseEventTargetImpl(int x, int y, boolean includeSelf, Container$EventTargetFilter filter, boolean searchHeavyweightChildren, boolean searchHeavyweightDescendants) {
        int ncomponents = this.ncomponents;
        Component[] component = this.component;
        for (int i = 0; i < ncomponents; i++) {
            Component comp = component[i];
            if (comp != null && comp.visible && ((!searchHeavyweightChildren && comp.peer instanceof LightweightPeer) || (searchHeavyweightChildren && !(comp.peer instanceof LightweightPeer))) && comp.contains(x - comp.x, y - comp.y)) {
                if (comp instanceof Container) {
                    Container child = (Container)(Container)comp;
                    Component deeper = child.getMouseEventTarget(x - child.x, y - child.y, includeSelf, filter, searchHeavyweightDescendants);
                    if (deeper != null) {
                        return deeper;
                    }
                } else {
                    if (filter.accept(comp)) {
                        return comp;
                    }
                }
            }
        }
        boolean isPeerOK;
        boolean isMouseOverMe;
        isPeerOK = (peer instanceof LightweightPeer) || includeSelf;
        isMouseOverMe = contains(x, y);
        if (isMouseOverMe && isPeerOK && filter.accept(this)) {
            return this;
        }
        return null;
    }
    {
    }
    {
    }
    {
    }
    
    void proxyEnableEvents(long events) {
        if (peer instanceof LightweightPeer) {
            if (parent != null) {
                parent.proxyEnableEvents(events);
            }
        } else {
            if (dispatcher != null) {
                dispatcher.enableEvents(events);
            }
        }
    }
    
    
    public void deliverEvent(Event e) {
        Component comp = getComponentAt(e.x, e.y);
        if ((comp != null) && (comp != this)) {
            e.translate(-comp.x, -comp.y);
            comp.deliverEvent(e);
        } else {
            postEvent(e);
        }
    }
    
    public Component getComponentAt(int x, int y) {
        return locate(x, y);
    }
    
    
    public Component locate(int x, int y) {
        if (!contains(x, y)) {
            return null;
        }
        synchronized (getTreeLock()) {
            for (int i = 0; i < ncomponents; i++) {
                Component comp = component[i];
                if (comp != null && !(comp.peer instanceof LightweightPeer)) {
                    if (comp.contains(x - comp.x, y - comp.y)) {
                        return comp;
                    }
                }
            }
            for (int i = 0; i < ncomponents; i++) {
                Component comp = component[i];
                if (comp != null && comp.peer instanceof LightweightPeer) {
                    if (comp.contains(x - comp.x, y - comp.y)) {
                        return comp;
                    }
                }
            }
        }
        return this;
    }
    
    public Component getComponentAt(Point p) {
        return getComponentAt(p.x, p.y);
    }
    
    public Point getMousePosition(boolean allowChildren) throws HeadlessException {
        if (GraphicsEnvironment.isHeadless()) {
            throw new HeadlessException();
        }
        PointerInfo pi = (PointerInfo)(PointerInfo)java.security.AccessController.doPrivileged(new Container$1(this));
        synchronized (getTreeLock()) {
            Component inTheSameWindow = findUnderMouseInWindow(pi);
            if (isSameOrAncestorOf(inTheSameWindow, allowChildren)) {
                return pointRelativeToComponent(pi.getLocation());
            }
            return null;
        }
    }
    
    boolean isSameOrAncestorOf(Component comp, boolean allowChildren) {
        return this == comp || (allowChildren && isParentOf(comp));
    }
    
    public Component findComponentAt(int x, int y) {
        synchronized (getTreeLock()) {
            return findComponentAt(x, y, true);
        }
    }
    
    final Component findComponentAt(int x, int y, boolean ignoreEnabled) {
        if (isRecursivelyVisible()) {
            return findComponentAtImpl(x, y, ignoreEnabled);
        }
        return null;
    }
    
    final Component findComponentAtImpl(int x, int y, boolean ignoreEnabled) {
        if (!(contains(x, y) && visible && (ignoreEnabled || enabled))) {
            return null;
        }
        int ncomponents = this.ncomponents;
        Component[] component = this.component;
        for (int i = 0; i < ncomponents; i++) {
            Component comp = component[i];
            if (comp != null && !(comp.peer instanceof LightweightPeer)) {
                if (comp instanceof Container) {
                    comp = ((Container)(Container)comp).findComponentAtImpl(x - comp.x, y - comp.y, ignoreEnabled);
                } else {
                    comp = comp.locate(x - comp.x, y - comp.y);
                }
                if (comp != null && comp.visible && (ignoreEnabled || comp.enabled)) {
                    return comp;
                }
            }
        }
        for (int i = 0; i < ncomponents; i++) {
            Component comp = component[i];
            if (comp != null && comp.peer instanceof LightweightPeer) {
                if (comp instanceof Container) {
                    comp = ((Container)(Container)comp).findComponentAtImpl(x - comp.x, y - comp.y, ignoreEnabled);
                } else {
                    comp = comp.locate(x - comp.x, y - comp.y);
                }
                if (comp != null && comp.visible && (ignoreEnabled || comp.enabled)) {
                    return comp;
                }
            }
        }
        return this;
    }
    
    public Component findComponentAt(Point p) {
        return findComponentAt(p.x, p.y);
    }
    
    public void addNotify() {
        synchronized (getTreeLock()) {
            super.addNotify();
            if (!(peer instanceof LightweightPeer)) {
                dispatcher = new LightweightDispatcher(this);
            }
            int ncomponents = this.ncomponents;
            Component[] component = this.component;
            for (int i = 0; i < ncomponents; i++) {
                component[i].addNotify();
            }
            ContainerPeer cpeer = (ContainerPeer)(ContainerPeer)peer;
            if (cpeer.isRestackSupported()) {
                cpeer.restack();
            }
        }
    }
    
    public void removeNotify() {
        synchronized (getTreeLock()) {
            int ncomponents = this.ncomponents;
            Component[] component = this.component;
            for (int i = ncomponents - 1; i >= 0; i--) {
                if (component[i] != null) component[i].removeNotify();
            }
            if (dispatcher != null) {
                dispatcher.dispose();
                dispatcher = null;
            }
            super.removeNotify();
        }
    }
    
    public boolean isAncestorOf(Component c) {
        Container p;
        if (c == null || ((p = c.getParent()) == null)) {
            return false;
        }
        while (p != null) {
            if (p == this) {
                return true;
            }
            p = p.getParent();
        }
        return false;
    }
    transient Component modalComp;
    transient AppContext modalAppContext;
    
    private void startLWModal() {
        modalAppContext = AppContext.getAppContext();
        long time = Toolkit.getEventQueue().getMostRecentEventTime();
        Component predictedFocusOwner = (this instanceof javax.swing.JInternalFrame) ? ((javax.swing.JInternalFrame)((javax.swing.JInternalFrame)this)).getMostRecentFocusOwner() : null;
        if (predictedFocusOwner != null) {
            KeyboardFocusManager.getCurrentKeyboardFocusManager().enqueueKeyEvents(time, predictedFocusOwner);
        }
        final Container nativeContainer;
        synchronized (getTreeLock()) {
            nativeContainer = getHeavyweightContainer();
            if (nativeContainer.modalComp != null) {
                this.modalComp = nativeContainer.modalComp;
                nativeContainer.modalComp = this;
                return;
            } else {
                nativeContainer.modalComp = this;
            }
        }
        Runnable pumpEventsForHierarchy = new Container$2(this, nativeContainer);
        if (EventQueue.isDispatchThread()) {
            SequencedEvent currentSequencedEvent = KeyboardFocusManager.getCurrentKeyboardFocusManager().getCurrentSequencedEvent();
            if (currentSequencedEvent != null) {
                currentSequencedEvent.dispose();
            }
            pumpEventsForHierarchy.run();
        } else {
            synchronized (getTreeLock()) {
                Toolkit.getEventQueue().postEvent(new PeerEvent(this, pumpEventsForHierarchy, PeerEvent.PRIORITY_EVENT));
                while (windowClosingException == null) {
                    try {
                        getTreeLock().wait();
                    } catch (InterruptedException e) {
                        break;
                    }
                }
            }
        }
        if (windowClosingException != null) {
            windowClosingException.fillInStackTrace();
            throw windowClosingException;
        }
        if (predictedFocusOwner != null) {
            KeyboardFocusManager.getCurrentKeyboardFocusManager().dequeueKeyEvents(time, predictedFocusOwner);
        }
    }
    
    private void stopLWModal() {
        synchronized (getTreeLock()) {
            if (modalAppContext != null) {
                Container nativeContainer = getHeavyweightContainer();
                if (nativeContainer != null) {
                    if (this.modalComp != null) {
                        nativeContainer.modalComp = this.modalComp;
                        this.modalComp = null;
                        return;
                    } else {
                        nativeContainer.modalComp = null;
                    }
                }
                SunToolkit.postEvent(modalAppContext, new PeerEvent(this, new Container$WakingRunnable(), PeerEvent.PRIORITY_EVENT));
            }
            EventQueue.invokeLater(new Container$WakingRunnable());
            getTreeLock().notifyAll();
        }
    }
    {
    }
    
    protected String paramString() {
        String str = super.paramString();
        LayoutManager layoutMgr = this.layoutMgr;
        if (layoutMgr != null) {
            str += ",layout=" + layoutMgr.getClass().getName();
        }
        return str;
    }
    
    public void list(PrintStream out, int indent) {
        super.list(out, indent);
        int ncomponents = this.ncomponents;
        Component[] component = this.component;
        for (int i = 0; i < ncomponents; i++) {
            Component comp = component[i];
            if (comp != null) {
                comp.list(out, indent + 1);
            }
        }
    }
    
    public void list(PrintWriter out, int indent) {
        super.list(out, indent);
        int ncomponents = this.ncomponents;
        Component[] component = this.component;
        for (int i = 0; i < ncomponents; i++) {
            Component comp = component[i];
            if (comp != null) {
                comp.list(out, indent + 1);
            }
        }
    }
    
    public void setFocusTraversalKeys(int id, Set keystrokes) {
        if (id < 0 || id >= KeyboardFocusManager.TRAVERSAL_KEY_LENGTH) {
            throw new IllegalArgumentException("invalid focus traversal key identifier");
        }
        setFocusTraversalKeys_NoIDCheck(id, keystrokes);
    }
    
    public Set getFocusTraversalKeys(int id) {
        if (id < 0 || id >= KeyboardFocusManager.TRAVERSAL_KEY_LENGTH) {
            throw new IllegalArgumentException("invalid focus traversal key identifier");
        }
        return getFocusTraversalKeys_NoIDCheck(id);
    }
    
    public boolean areFocusTraversalKeysSet(int id) {
        if (id < 0 || id >= KeyboardFocusManager.TRAVERSAL_KEY_LENGTH) {
            throw new IllegalArgumentException("invalid focus traversal key identifier");
        }
        return (focusTraversalKeys != null && focusTraversalKeys[id] != null);
    }
    
    public boolean isFocusCycleRoot(Container container) {
        if (isFocusCycleRoot() && container == this) {
            return true;
        } else {
            return super.isFocusCycleRoot(container);
        }
    }
    
    private Container findTraversalRoot() {
        Container currentFocusCycleRoot = KeyboardFocusManager.getCurrentKeyboardFocusManager().getCurrentFocusCycleRoot();
        Container root;
        if (currentFocusCycleRoot == this) {
            root = this;
        } else {
            root = getFocusCycleRootAncestor();
            if (root == null) {
                root = this;
            }
        }
        if (root != currentFocusCycleRoot) {
            KeyboardFocusManager.getCurrentKeyboardFocusManager().setGlobalCurrentFocusCycleRoot(root);
        }
        return root;
    }
    
    final boolean containsFocus() {
        synchronized (getTreeLock()) {
            Component comp = KeyboardFocusManager.getCurrentKeyboardFocusManager().getFocusOwner();
            while (comp != null && !(comp instanceof Window) && comp != this) {
                comp = (Component)comp.getParent();
            }
            return (comp == this);
        }
    }
    
    boolean isParentOf(Component comp) {
        synchronized (getTreeLock()) {
            while (comp != null && comp != this && !(comp instanceof Window)) {
                comp = comp.getParent();
            }
            return (comp == this);
        }
    }
    
    void clearMostRecentFocusOwnerOnHide() {
        Component comp = null;
        Container window = this;
        synchronized (getTreeLock()) {
            while (window != null && !(window instanceof Window)) {
                window = window.getParent();
            }
            if (window != null) {
                comp = KeyboardFocusManager.getMostRecentFocusOwner((Window)(Window)window);
                while ((comp != null) && (comp != this) && !(comp instanceof Window)) {
                    comp = comp.getParent();
                }
            }
        }
        if (comp == this) {
            KeyboardFocusManager.setMostRecentFocusOwner((Window)(Window)window, null);
        }
        if (window != null) {
            Window myWindow = (Window)(Window)window;
            synchronized (getTreeLock()) {
                synchronized (KeyboardFocusManager.class) {
                    Component storedComp = myWindow.getTemporaryLostComponent();
                    if (isParentOf(storedComp) || storedComp == this) {
                        myWindow.setTemporaryLostComponent(null);
                    }
                }
            }
        }
    }
    
    void clearCurrentFocusCycleRootOnHide() {
        KeyboardFocusManager kfm = KeyboardFocusManager.getCurrentKeyboardFocusManager();
        Container cont = kfm.getCurrentFocusCycleRoot();
        synchronized (getTreeLock()) {
            while (this != cont && !(cont instanceof Window) && (cont != null)) {
                cont = cont.getParent();
            }
        }
        if (cont == this) {
            kfm.setGlobalCurrentFocusCycleRoot(null);
        }
    }
    
    boolean nextFocusHelper() {
        if (isFocusCycleRoot()) {
            Container root = findTraversalRoot();
            Component comp = this;
            Container anc;
            while (root != null && (anc = root.getFocusCycleRootAncestor()) != null && !(root.isShowing() && root.isFocusable() && root.isEnabled())) {
                comp = root;
                root = anc;
            }
            if (root != null) {
                FocusTraversalPolicy policy = root.getFocusTraversalPolicy();
                Component toFocus = policy.getComponentAfter(root, comp);
                if (toFocus == null) {
                    toFocus = policy.getDefaultComponent(root);
                }
                if (toFocus != null) {
                    return toFocus.requestFocus(false);
                }
            }
            return false;
        } else {
            return super.nextFocusHelper();
        }
    }
    
    public void transferFocusBackward() {
        if (isFocusCycleRoot()) {
            Container root = findTraversalRoot();
            Component comp = this;
            while (root != null && !(root.isShowing() && root.isFocusable() && root.isEnabled())) {
                comp = root;
                root = comp.getFocusCycleRootAncestor();
            }
            if (root != null) {
                FocusTraversalPolicy policy = root.getFocusTraversalPolicy();
                Component toFocus = policy.getComponentBefore(root, comp);
                if (toFocus == null) {
                    toFocus = policy.getDefaultComponent(root);
                }
                if (toFocus != null) {
                    toFocus.requestFocus();
                }
            }
        } else {
            super.transferFocusBackward();
        }
    }
    
    public void setFocusTraversalPolicy(FocusTraversalPolicy policy) {
        FocusTraversalPolicy oldPolicy;
        synchronized (this) {
            oldPolicy = this.focusTraversalPolicy;
            this.focusTraversalPolicy = policy;
        }
        firePropertyChange("focusTraversalPolicy", oldPolicy, policy);
    }
    
    public FocusTraversalPolicy getFocusTraversalPolicy() {
        if (!isFocusTraversalPolicyProvider() && !isFocusCycleRoot()) {
            return null;
        }
        FocusTraversalPolicy policy = this.focusTraversalPolicy;
        if (policy != null) {
            return policy;
        }
        Container rootAncestor = getFocusCycleRootAncestor();
        if (rootAncestor != null) {
            return rootAncestor.getFocusTraversalPolicy();
        } else {
            return KeyboardFocusManager.getCurrentKeyboardFocusManager().getDefaultFocusTraversalPolicy();
        }
    }
    
    public boolean isFocusTraversalPolicySet() {
        return (focusTraversalPolicy != null);
    }
    
    public void setFocusCycleRoot(boolean focusCycleRoot) {
        boolean oldFocusCycleRoot;
        synchronized (this) {
            oldFocusCycleRoot = this.focusCycleRoot;
            this.focusCycleRoot = focusCycleRoot;
        }
        firePropertyChange("focusCycleRoot", oldFocusCycleRoot, focusCycleRoot);
    }
    
    public boolean isFocusCycleRoot() {
        return focusCycleRoot;
    }
    
    public final void setFocusTraversalPolicyProvider(boolean provider) {
        boolean oldProvider;
        synchronized (this) {
            oldProvider = focusTraversalPolicyProvider;
            focusTraversalPolicyProvider = provider;
        }
        firePropertyChange("focusTraversalPolicyProvider", oldProvider, provider);
    }
    
    public final boolean isFocusTraversalPolicyProvider() {
        return focusTraversalPolicyProvider;
    }
    
    public void transferFocusDownCycle() {
        if (isFocusCycleRoot()) {
            KeyboardFocusManager.getCurrentKeyboardFocusManager().setGlobalCurrentFocusCycleRoot(this);
            Component toFocus = getFocusTraversalPolicy().getDefaultComponent(this);
            if (toFocus != null) {
                toFocus.requestFocus();
            }
        }
    }
    
    void preProcessKeyEvent(KeyEvent e) {
        Container parent = this.parent;
        if (parent != null) {
            parent.preProcessKeyEvent(e);
        }
    }
    
    void postProcessKeyEvent(KeyEvent e) {
        Container parent = this.parent;
        if (parent != null) {
            parent.postProcessKeyEvent(e);
        }
    }
    
    boolean postsOldMouseEvents() {
        return true;
    }
    
    public void applyComponentOrientation(ComponentOrientation o) {
        super.applyComponentOrientation(o);
        for (int i = 0; i < ncomponents; ++i) {
            component[i].applyComponentOrientation(o);
        }
    }
    
    public void addPropertyChangeListener(PropertyChangeListener listener) {
        super.addPropertyChangeListener(listener);
    }
    
    public void addPropertyChangeListener(String propertyName, PropertyChangeListener listener) {
        super.addPropertyChangeListener(propertyName, listener);
    }
    private int containerSerializedDataVersion = 1;
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        ObjectOutputStream$PutField f = s.putFields();
        f.put("ncomponents", ncomponents);
        f.put("component", component);
        f.put("layoutMgr", layoutMgr);
        f.put("dispatcher", dispatcher);
        f.put("maxSize", maxSize);
        f.put("focusCycleRoot", focusCycleRoot);
        f.put("containerSerializedDataVersion", containerSerializedDataVersion);
        f.put("focusTraversalPolicyProvider", focusTraversalPolicyProvider);
        s.writeFields();
        AWTEventMulticaster.save(s, containerListenerK, containerListener);
        s.writeObject(null);
        if (focusTraversalPolicy instanceof java.io.Serializable) {
            s.writeObject(focusTraversalPolicy);
        } else {
            s.writeObject(null);
        }
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException {
        ObjectInputStream$GetField f = s.readFields();
        ncomponents = f.get("ncomponents", 0);
        component = (Component[])(Component[])f.get("component", new Component[0]);
        layoutMgr = (LayoutManager)(LayoutManager)f.get("layoutMgr", null);
        dispatcher = (LightweightDispatcher)(LightweightDispatcher)f.get("dispatcher", null);
        if (maxSize == null) {
            maxSize = (Dimension)(Dimension)f.get("maxSize", null);
        }
        focusCycleRoot = f.get("focusCycleRoot", false);
        containerSerializedDataVersion = f.get("containerSerializedDataVersion", 1);
        focusTraversalPolicyProvider = f.get("focusTraversalPolicyProvider", false);
        Component[] component = this.component;
        for (int i = 0; i < ncomponents; i++) {
            component[i].parent = this;
            adjustListeningChildren(AWTEvent.HIERARCHY_EVENT_MASK, component[i].numListening(AWTEvent.HIERARCHY_EVENT_MASK));
            adjustListeningChildren(AWTEvent.HIERARCHY_BOUNDS_EVENT_MASK, component[i].numListening(AWTEvent.HIERARCHY_BOUNDS_EVENT_MASK));
            adjustDescendants(component[i].countHierarchyMembers());
        }
        Object keyOrNull;
        while (null != (keyOrNull = s.readObject())) {
            String key = ((String)(String)keyOrNull).intern();
            if (containerListenerK == key) {
                addContainerListener((ContainerListener)((ContainerListener)s.readObject()));
            } else {
                s.readObject();
            }
        }
        try {
            Object policy = s.readObject();
            if (policy instanceof FocusTraversalPolicy) {
                focusTraversalPolicy = (FocusTraversalPolicy)(FocusTraversalPolicy)policy;
            }
        } catch (java.io.OptionalDataException e) {
            if (!e.eof) {
                throw e;
            }
        }
    }
    {
    }
    
    Accessible getAccessibleAt(Point p) {
        synchronized (getTreeLock()) {
            if (this instanceof Accessible) {
                Accessible a = (Accessible)(Accessible)this;
                AccessibleContext ac = a.getAccessibleContext();
                if (ac != null) {
                    AccessibleComponent acmp;
                    Point location;
                    int nchildren = ac.getAccessibleChildrenCount();
                    for (int i = 0; i < nchildren; i++) {
                        a = ac.getAccessibleChild(i);
                        if (a != null) {
                            ac = a.getAccessibleContext();
                            if (ac != null) {
                                acmp = ac.getAccessibleComponent();
                                if ((acmp != null) && (acmp.isShowing())) {
                                    location = acmp.getLocation();
                                    Point np = new Point(p.x - location.x, p.y - location.y);
                                    if (acmp.contains(np)) {
                                        return a;
                                    }
                                }
                            }
                        }
                    }
                }
                return (Accessible)(Accessible)this;
            } else {
                Component ret = this;
                if (!this.contains(p.x, p.y)) {
                    ret = null;
                } else {
                    int ncomponents = this.getComponentCount();
                    for (int i = 0; i < ncomponents; i++) {
                        Component comp = this.getComponent(i);
                        if ((comp != null) && comp.isShowing()) {
                            Point location = comp.getLocation();
                            if (comp.contains(p.x - location.x, p.y - location.y)) {
                                ret = comp;
                            }
                        }
                    }
                }
                if (ret instanceof Accessible) {
                    return (Accessible)(Accessible)ret;
                }
            }
            return null;
        }
    }
    
    int getAccessibleChildrenCount() {
        synchronized (getTreeLock()) {
            int count = 0;
            Component[] children = this.getComponents();
            for (int i = 0; i < children.length; i++) {
                if (children[i] instanceof Accessible) {
                    count++;
                }
            }
            return count;
        }
    }
    
    Accessible getAccessibleChild(int i) {
        synchronized (getTreeLock()) {
            Component[] children = this.getComponents();
            int count = 0;
            for (int j = 0; j < children.length; j++) {
                if (children[j] instanceof Accessible) {
                    if (count == i) {
                        return (Accessible)(Accessible)children[j];
                    } else {
                        count++;
                    }
                }
            }
            return null;
        }
    }
}
