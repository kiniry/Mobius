package java.awt;

import java.util.Hashtable;
import java.util.Vector;
import java.util.Enumeration;
import java.io.Serializable;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.ObjectStreamField;
import java.io.IOException;

public class CardLayout implements LayoutManager2, Serializable {
    private static final long serialVersionUID = -4328196481005934313L;
    Vector vector = new Vector();
    {
    }
    int currentCard = 0;
    int hgap;
    int vgap;
    private static final ObjectStreamField[] serialPersistentFields = {new ObjectStreamField("tab", Hashtable.class), new ObjectStreamField("hgap", Integer.TYPE), new ObjectStreamField("vgap", Integer.TYPE), new ObjectStreamField("vector", Vector.class), new ObjectStreamField("currentCard", Integer.TYPE)};
    
    public CardLayout() {
        this(0, 0);
    }
    
    public CardLayout(int hgap, int vgap) {
        
        this.hgap = hgap;
        this.vgap = vgap;
    }
    
    public int getHgap() {
        return hgap;
    }
    
    public void setHgap(int hgap) {
        this.hgap = hgap;
    }
    
    public int getVgap() {
        return vgap;
    }
    
    public void setVgap(int vgap) {
        this.vgap = vgap;
    }
    
    public void addLayoutComponent(Component comp, Object constraints) {
        synchronized (comp.getTreeLock()) {
            if (constraints instanceof String) {
                addLayoutComponent((String)(String)constraints, comp);
            } else {
                throw new IllegalArgumentException("cannot add to layout: constraint must be a string");
            }
        }
    }
    
    
    public void addLayoutComponent(String name, Component comp) {
        synchronized (comp.getTreeLock()) {
            if (!vector.isEmpty()) {
                comp.setVisible(false);
            }
            for (int i = 0; i < vector.size(); i++) {
                if (((CardLayout$Card)(CardLayout$Card)vector.get(i)).name.equals(name)) {
                    ((CardLayout$Card)(CardLayout$Card)vector.get(i)).comp = comp;
                    return;
                }
            }
            vector.add(new CardLayout$Card(this, name, comp));
        }
    }
    
    public void removeLayoutComponent(Component comp) {
        synchronized (comp.getTreeLock()) {
            for (int i = 0; i < vector.size(); i++) {
                if (((CardLayout$Card)(CardLayout$Card)vector.get(i)).comp == comp) {
                    if (comp.isVisible() && (comp.getParent() != null)) {
                        next(comp.getParent());
                    }
                    vector.remove(i);
                    if (currentCard > i) {
                        currentCard--;
                    }
                    break;
                }
            }
        }
    }
    
    public Dimension preferredLayoutSize(Container parent) {
        synchronized (parent.getTreeLock()) {
            Insets insets = parent.getInsets();
            int ncomponents = parent.getComponentCount();
            int w = 0;
            int h = 0;
            for (int i = 0; i < ncomponents; i++) {
                Component comp = parent.getComponent(i);
                Dimension d = comp.getPreferredSize();
                if (d.width > w) {
                    w = d.width;
                }
                if (d.height > h) {
                    h = d.height;
                }
            }
            return new Dimension(insets.left + insets.right + w + hgap * 2, insets.top + insets.bottom + h + vgap * 2);
        }
    }
    
    public Dimension minimumLayoutSize(Container parent) {
        synchronized (parent.getTreeLock()) {
            Insets insets = parent.getInsets();
            int ncomponents = parent.getComponentCount();
            int w = 0;
            int h = 0;
            for (int i = 0; i < ncomponents; i++) {
                Component comp = parent.getComponent(i);
                Dimension d = comp.getMinimumSize();
                if (d.width > w) {
                    w = d.width;
                }
                if (d.height > h) {
                    h = d.height;
                }
            }
            return new Dimension(insets.left + insets.right + w + hgap * 2, insets.top + insets.bottom + h + vgap * 2);
        }
    }
    
    public Dimension maximumLayoutSize(Container target) {
        return new Dimension(Integer.MAX_VALUE, Integer.MAX_VALUE);
    }
    
    public float getLayoutAlignmentX(Container parent) {
        return 0.5F;
    }
    
    public float getLayoutAlignmentY(Container parent) {
        return 0.5F;
    }
    
    public void invalidateLayout(Container target) {
    }
    
    public void layoutContainer(Container parent) {
        synchronized (parent.getTreeLock()) {
            Insets insets = parent.getInsets();
            int ncomponents = parent.getComponentCount();
            Component comp = null;
            boolean currentFound = false;
            for (int i = 0; i < ncomponents; i++) {
                comp = parent.getComponent(i);
                comp.setBounds(hgap + insets.left, vgap + insets.top, parent.width - (hgap * 2 + insets.left + insets.right), parent.height - (vgap * 2 + insets.top + insets.bottom));
                if (comp.isVisible()) {
                    currentFound = true;
                }
            }
            if (!currentFound && ncomponents > 0) {
                parent.getComponent(0).setVisible(true);
            }
        }
    }
    
    void checkLayout(Container parent) {
        if (parent.getLayout() != this) {
            throw new IllegalArgumentException("wrong parent for CardLayout");
        }
    }
    
    public void first(Container parent) {
        synchronized (parent.getTreeLock()) {
            checkLayout(parent);
            int ncomponents = parent.getComponentCount();
            for (int i = 0; i < ncomponents; i++) {
                Component comp = parent.getComponent(i);
                if (comp.isVisible()) {
                    comp.setVisible(false);
                    break;
                }
            }
            if (ncomponents > 0) {
                currentCard = 0;
                parent.getComponent(0).setVisible(true);
                parent.validate();
            }
        }
    }
    
    public void next(Container parent) {
        synchronized (parent.getTreeLock()) {
            checkLayout(parent);
            int ncomponents = parent.getComponentCount();
            for (int i = 0; i < ncomponents; i++) {
                Component comp = parent.getComponent(i);
                if (comp.isVisible()) {
                    comp.setVisible(false);
                    currentCard = (i + 1) % ncomponents;
                    comp = parent.getComponent(currentCard);
                    comp.setVisible(true);
                    parent.validate();
                    return;
                }
            }
            showDefaultComponent(parent);
        }
    }
    
    public void previous(Container parent) {
        synchronized (parent.getTreeLock()) {
            checkLayout(parent);
            int ncomponents = parent.getComponentCount();
            for (int i = 0; i < ncomponents; i++) {
                Component comp = parent.getComponent(i);
                if (comp.isVisible()) {
                    comp.setVisible(false);
                    currentCard = ((i > 0) ? i - 1 : ncomponents - 1);
                    comp = parent.getComponent(currentCard);
                    comp.setVisible(true);
                    parent.validate();
                    return;
                }
            }
            showDefaultComponent(parent);
        }
    }
    
    void showDefaultComponent(Container parent) {
        if (parent.getComponentCount() > 0) {
            currentCard = 0;
            parent.getComponent(0).setVisible(true);
            parent.validate();
        }
    }
    
    public void last(Container parent) {
        synchronized (parent.getTreeLock()) {
            checkLayout(parent);
            int ncomponents = parent.getComponentCount();
            for (int i = 0; i < ncomponents; i++) {
                Component comp = parent.getComponent(i);
                if (comp.isVisible()) {
                    comp.setVisible(false);
                    break;
                }
            }
            if (ncomponents > 0) {
                currentCard = ncomponents - 1;
                parent.getComponent(currentCard).setVisible(true);
                parent.validate();
            }
        }
    }
    
    public void show(Container parent, String name) {
        synchronized (parent.getTreeLock()) {
            checkLayout(parent);
            Component next = null;
            int ncomponents = vector.size();
            for (int i = 0; i < ncomponents; i++) {
                CardLayout$Card card = (CardLayout$Card)(CardLayout$Card)vector.get(i);
                if (card.name.equals(name)) {
                    next = card.comp;
                    currentCard = i;
                    break;
                }
            }
            if ((next != null) && !next.isVisible()) {
                ncomponents = parent.getComponentCount();
                for (int i = 0; i < ncomponents; i++) {
                    Component comp = parent.getComponent(i);
                    if (comp.isVisible()) {
                        comp.setVisible(false);
                        break;
                    }
                }
                next.setVisible(true);
                parent.validate();
            }
        }
    }
    
    public String toString() {
        return getClass().getName() + "[hgap=" + hgap + ",vgap=" + vgap + "]";
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException {
        ObjectInputStream$GetField f = s.readFields();
        hgap = f.get("hgap", 0);
        vgap = f.get("vgap", 0);
        if (f.defaulted("vector")) {
            Hashtable tab = (Hashtable)(Hashtable)f.get("tab", null);
            vector = new Vector();
            if (tab != null && !tab.isEmpty()) {
                for (Enumeration e = tab.keys(); e.hasMoreElements(); ) {
                    String key = (String)(String)e.nextElement();
                    Component comp = (Component)(Component)tab.get(key);
                    vector.add(new CardLayout$Card(this, key, comp));
                    if (comp.isVisible()) {
                        currentCard = vector.size() - 1;
                    }
                }
            }
        } else {
            vector = (Vector)(Vector)f.get("vector", null);
            currentCard = f.get("currentCard", 0);
        }
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        Hashtable tab = new Hashtable();
        int ncomponents = vector.size();
        for (int i = 0; i < ncomponents; i++) {
            CardLayout$Card card = (CardLayout$Card)(CardLayout$Card)vector.get(i);
            tab.put(card.name, card.comp);
        }
        ObjectOutputStream$PutField f = s.putFields();
        f.put("hgap", hgap);
        f.put("vgap", vgap);
        f.put("vector", vector);
        f.put("currentCard", currentCard);
        f.put("tab", tab);
        s.writeFields();
    }
}
