package javax.swing;

import java.util.*;
import java.awt.*;
import java.awt.event.*;
import java.applet.*;
import java.beans.*;
import javax.swing.event.*;

class KeyboardManager {
    
    KeyboardManager() {
        
    }
    static KeyboardManager currentManager = new KeyboardManager();
    Hashtable containerMap = new Hashtable();
    Hashtable componentKeyStrokeMap = new Hashtable();
    
    public static KeyboardManager getCurrentManager() {
        return currentManager;
    }
    
    public static void setCurrentManager(KeyboardManager km) {
        currentManager = km;
    }
    
    public void registerKeyStroke(KeyStroke k, JComponent c) {
        Container topContainer = getTopAncestor(c);
        if (topContainer == null) {
            return;
        }
        Hashtable keyMap = (Hashtable)(Hashtable)containerMap.get(topContainer);
        if (keyMap == null) {
            keyMap = registerNewTopContainer(topContainer);
        }
        Object tmp = keyMap.get(k);
        if (tmp == null) {
            keyMap.put(k, c);
        } else if (tmp instanceof Vector) {
            Vector v = (Vector)(Vector)tmp;
            if (!v.contains(c)) {
                v.addElement(c);
            }
        } else if (tmp instanceof JComponent) {
            if (tmp != c) {
                Vector v = new Vector();
                v.addElement(tmp);
                v.addElement(c);
                keyMap.put(k, v);
            }
        } else {
            System.out.println("Unexpected condition in registerKeyStroke");
            Thread.dumpStack();
        }
        componentKeyStrokeMap.put(new KeyboardManager$ComponentKeyStrokePair(this, c, k), topContainer);
    }
    
    private static Container getTopAncestor(JComponent c) {
        for (Container p = c.getParent(); p != null; p = p.getParent()) {
            if (p instanceof Window && ((Window)(Window)p).isFocusableWindow() || p instanceof Applet || p instanceof JInternalFrame) {
                return p;
            }
        }
        return null;
    }
    
    public void unregisterKeyStroke(KeyStroke ks, JComponent c) {
        KeyboardManager$ComponentKeyStrokePair ckp = new KeyboardManager$ComponentKeyStrokePair(this, c, ks);
        Object topContainer = componentKeyStrokeMap.get(ckp);
        if (topContainer == null) {
            return;
        }
        Hashtable keyMap = (Hashtable)(Hashtable)containerMap.get(topContainer);
        if (keyMap == null) {
            Thread.dumpStack();
            return;
        }
        Object tmp = keyMap.get(ks);
        if (tmp == null) {
            Thread.dumpStack();
            return;
        }
        if (tmp instanceof JComponent && tmp == c) {
            keyMap.remove(ks);
        } else if (tmp instanceof Vector) {
            Vector v = (Vector)(Vector)tmp;
            v.removeElement(c);
            if (v.isEmpty()) {
                keyMap.remove(ks);
            }
        }
        if (keyMap.isEmpty()) {
            containerMap.remove(topContainer);
        }
        componentKeyStrokeMap.remove(ckp);
    }
    
    public boolean fireKeyboardAction(KeyEvent e, boolean pressed, Container topAncestor) {
        if (e.isConsumed()) {
            System.out.println("Aquired pre-used event!");
            Thread.dumpStack();
        }
        KeyStroke ks;
        if (e.getID() == KeyEvent.KEY_TYPED) {
            ks = KeyStroke.getKeyStroke(e.getKeyChar());
        } else {
            ks = KeyStroke.getKeyStroke(e.getKeyCode(), e.getModifiers(), !pressed);
        }
        Hashtable keyMap = (Hashtable)(Hashtable)containerMap.get(topAncestor);
        if (keyMap != null) {
            Object tmp = keyMap.get(ks);
            if (tmp == null) {
            } else if (tmp instanceof JComponent) {
                JComponent c = (JComponent)(JComponent)tmp;
                if (c.isShowing() && c.isEnabled()) {
                    fireBinding(c, ks, e, pressed);
                }
            } else if (tmp instanceof Vector) {
                Vector v = (Vector)(Vector)tmp;
                for (int counter = v.size() - 1; counter >= 0; counter--) {
                    JComponent c = (JComponent)(JComponent)v.elementAt(counter);
                    if (c.isShowing() && c.isEnabled()) {
                        fireBinding(c, ks, e, pressed);
                        if (e.isConsumed()) return true;
                    }
                }
            } else {
                System.out.println("Unexpected condition in fireKeyboardAction " + tmp);
                Thread.dumpStack();
            }
        }
        if (e.isConsumed()) {
            return true;
        }
        if (keyMap != null) {
            Vector v = (Vector)(Vector)keyMap.get(JMenuBar.class);
            if (v != null) {
                Enumeration iter = v.elements();
                while (iter.hasMoreElements()) {
                    JMenuBar mb = (JMenuBar)(JMenuBar)iter.nextElement();
                    if (mb.isShowing() && mb.isEnabled()) {
                        fireBinding(mb, ks, e, pressed);
                        if (e.isConsumed()) {
                            return true;
                        }
                    }
                }
            }
        }
        return e.isConsumed();
    }
    
    void fireBinding(JComponent c, KeyStroke ks, KeyEvent e, boolean pressed) {
        if (c.processKeyBinding(ks, e, JComponent.WHEN_IN_FOCUSED_WINDOW, pressed)) {
            e.consume();
        }
    }
    
    public void registerMenuBar(JMenuBar mb) {
        Container top = getTopAncestor(mb);
        Hashtable keyMap = (Hashtable)(Hashtable)containerMap.get(top);
        if (keyMap == null) {
            keyMap = registerNewTopContainer(top);
        }
        Vector menuBars = (Vector)(Vector)keyMap.get(JMenuBar.class);
        if (menuBars == null) {
            menuBars = new Vector();
            keyMap.put(JMenuBar.class, menuBars);
        }
        if (!menuBars.contains(mb)) {
            menuBars.addElement(mb);
        }
    }
    
    public void unregisterMenuBar(JMenuBar mb) {
        Object topContainer = getTopAncestor(mb);
        Hashtable keyMap = (Hashtable)(Hashtable)containerMap.get(topContainer);
        if (keyMap != null) {
            Vector v = (Vector)(Vector)keyMap.get(JMenuBar.class);
            if (v != null) {
                v.removeElement(mb);
                if (v.isEmpty()) {
                    keyMap.remove(JMenuBar.class);
                    if (keyMap.isEmpty()) {
                        containerMap.remove(topContainer);
                    }
                }
            }
        }
    }
    
    protected Hashtable registerNewTopContainer(Container topContainer) {
        Hashtable keyMap = new Hashtable();
        containerMap.put(topContainer, keyMap);
        return keyMap;
    }
    {
    }
}
