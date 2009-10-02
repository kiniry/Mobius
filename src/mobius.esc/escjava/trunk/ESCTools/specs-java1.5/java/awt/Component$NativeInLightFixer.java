package java.awt;

import java.util.Vector;
import java.awt.peer.ComponentPeer;
import java.awt.peer.LightweightPeer;
import java.awt.event.*;
import javax.accessibility.*;
import javax.accessibility.*;
import java.util.logging.*;

final class Component$NativeInLightFixer implements ComponentListener, ContainerListener {
    /*synthetic*/ final Component this$0;
    
    Component$NativeInLightFixer(/*synthetic*/ final Component this$0) {
        this.this$0 = this$0;
        
        lightParents = new Vector();
        install(this$0.parent);
    }
    
    void install(Container parent) {
        lightParents.clear();
        Container p = parent;
        boolean isLwParentsVisible = true;
        for (; p.peer instanceof LightweightPeer; p = p.parent) {
            p.addComponentListener(this);
            p.addContainerListener(this);
            lightParents.addElement(p);
            isLwParentsVisible &= p.isVisible();
        }
        nativeHost = p;
        p.addContainerListener(this);
        componentMoved(null);
        if (!isLwParentsVisible) {
            synchronized (this$0.getTreeLock()) {
                if (this$0.peer != null) {
                    this$0.peer.hide();
                }
            }
        }
    }
    
    public void componentResized(ComponentEvent e) {
    }
    
    public void componentMoved(ComponentEvent e) {
        synchronized (this$0.getTreeLock()) {
            int nativeX = this$0.x;
            int nativeY = this$0.y;
            for (Component c = this$0.parent; (c != null) && (c.peer instanceof LightweightPeer); c = c.parent) {
                nativeX += c.x;
                nativeY += c.y;
            }
            if (this$0.peer != null) {
                this$0.peer.setBounds(nativeX, nativeY, this$0.width, this$0.height, ComponentPeer.SET_LOCATION);
            }
        }
    }
    
    public void componentShown(ComponentEvent e) {
        if (this$0.isShowing()) {
            synchronized (this$0.getTreeLock()) {
                if (this$0.peer != null) {
                    this$0.peer.show();
                }
            }
        }
    }
    
    public void componentHidden(ComponentEvent e) {
        if (this$0.visible) {
            synchronized (this$0.getTreeLock()) {
                if (this$0.peer != null) {
                    this$0.peer.hide();
                }
            }
        }
    }
    
    public void componentAdded(ContainerEvent e) {
    }
    
    public void componentRemoved(ContainerEvent e) {
        Component c = e.getChild();
        if (c == this$0) {
            removeReferences();
        } else {
            int n = lightParents.size();
            for (int i = 0; i < n; i++) {
                Container p = (Container)(Container)lightParents.elementAt(i);
                if (p == c) {
                    removeReferences();
                    break;
                }
            }
        }
    }
    
    void removeReferences() {
        int n = lightParents.size();
        for (int i = 0; i < n; i++) {
            Container c = (Container)(Container)lightParents.elementAt(i);
            c.removeComponentListener(this);
            c.removeContainerListener(this);
        }
        nativeHost.removeContainerListener(this);
        lightParents.clear();
        nativeHost = null;
    }
    Vector lightParents;
    Container nativeHost;
}
