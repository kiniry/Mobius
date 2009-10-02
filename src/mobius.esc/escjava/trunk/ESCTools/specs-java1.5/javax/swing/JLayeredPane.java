package javax.swing;

import java.awt.Component;
import java.util.ArrayList;
import java.util.Hashtable;
import java.awt.Color;
import java.awt.Graphics;
import java.awt.Rectangle;
import javax.accessibility.*;

public class JLayeredPane extends JComponent implements Accessible {
    public static final Integer DEFAULT_LAYER = new Integer(0);
    public static final Integer PALETTE_LAYER = new Integer(100);
    public static final Integer MODAL_LAYER = new Integer(200);
    public static final Integer POPUP_LAYER = new Integer(300);
    public static final Integer DRAG_LAYER = new Integer(400);
    public static final Integer FRAME_CONTENT_LAYER = new Integer(-30000);
    public static final String LAYER_PROPERTY = "layeredContainerLayer";
    private Hashtable componentToLayer;
    private boolean optimizedDrawingPossible = true;
    
    public JLayeredPane() {
        
        setLayout(null);
    }
    
    private void validateOptimizedDrawing() {
        boolean layeredComponentFound = false;
        synchronized (getTreeLock()) {
            Integer layer = null;
            for (Component[] arr$ = getComponents(), len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
                Component c = arr$[i$];
                {
                    layer = null;
                    if (c instanceof JInternalFrame || (c instanceof JComponent && (layer = (Integer)(Integer)((JComponent)(JComponent)c).getClientProperty(LAYER_PROPERTY)) != null)) {
                        if (layer != null && layer.equals(FRAME_CONTENT_LAYER)) continue;
                        layeredComponentFound = true;
                        break;
                    }
                }
            }
        }
        if (layeredComponentFound) optimizedDrawingPossible = false; else optimizedDrawingPossible = true;
    }
    
    protected void addImpl(Component comp, Object constraints, int index) {
        int layer = DEFAULT_LAYER.intValue();
        int pos;
        if (constraints instanceof Integer) {
            layer = ((Integer)(Integer)constraints).intValue();
            setLayer(comp, layer);
        } else layer = getLayer(comp);
        pos = insertIndexForLayer(layer, index);
        super.addImpl(comp, constraints, pos);
        comp.validate();
        comp.repaint();
        validateOptimizedDrawing();
    }
    
    public void remove(int index) {
        Component c = getComponent(index);
        super.remove(index);
        if (c != null && !(c instanceof JComponent)) {
            getComponentToLayer().remove(c);
        }
        validateOptimizedDrawing();
    }
    
    public void removeAll() {
        Component[] children = getComponents();
        Hashtable cToL = getComponentToLayer();
        for (int counter = children.length - 1; counter >= 0; counter--) {
            Component c = children[counter];
            if (c != null && !(c instanceof JComponent)) {
                cToL.remove(c);
            }
        }
        super.removeAll();
    }
    
    public boolean isOptimizedDrawingEnabled() {
        return optimizedDrawingPossible;
    }
    
    public static void putLayer(JComponent c, int layer) {
        Integer layerObj;
        layerObj = new Integer(layer);
        c.putClientProperty(LAYER_PROPERTY, layerObj);
    }
    
    public static int getLayer(JComponent c) {
        Integer i;
        if ((i = (Integer)(Integer)c.getClientProperty(LAYER_PROPERTY)) != null) return i.intValue();
        return DEFAULT_LAYER.intValue();
    }
    
    public static JLayeredPane getLayeredPaneAbove(Component c) {
        if (c == null) return null;
        Component parent = c.getParent();
        while (parent != null && !(parent instanceof JLayeredPane)) parent = parent.getParent();
        return (JLayeredPane)(JLayeredPane)parent;
    }
    
    public void setLayer(Component c, int layer) {
        setLayer(c, layer, -1);
    }
    
    public void setLayer(Component c, int layer, int position) {
        Integer layerObj;
        layerObj = getObjectForLayer(layer);
        if (layer == getLayer(c) && position == getPosition(c)) {
            repaint(c.getBounds());
            return;
        }
        if (c instanceof JComponent) ((JComponent)(JComponent)c).putClientProperty(LAYER_PROPERTY, layerObj); else getComponentToLayer().put((Component)c, layerObj);
        if (c.getParent() == null || c.getParent() != this) {
            repaint(c.getBounds());
            return;
        }
        int index = insertIndexForLayer(c, layer, position);
        setComponentZOrder(c, index);
        repaint(c.getBounds());
    }
    
    public int getLayer(Component c) {
        Integer i;
        if (c instanceof JComponent) i = (Integer)(Integer)((JComponent)(JComponent)c).getClientProperty(LAYER_PROPERTY); else i = (Integer)(Integer)getComponentToLayer().get((Component)c);
        if (i == null) return DEFAULT_LAYER.intValue();
        return i.intValue();
    }
    
    public int getIndexOf(Component c) {
        int i;
        int count;
        count = getComponentCount();
        for (i = 0; i < count; i++) {
            if (c == getComponent(i)) return i;
        }
        return -1;
    }
    
    public void moveToFront(Component c) {
        setPosition(c, 0);
    }
    
    public void moveToBack(Component c) {
        setPosition(c, -1);
    }
    
    public void setPosition(Component c, int position) {
        setLayer(c, getLayer(c), position);
    }
    
    public int getPosition(Component c) {
        int i;
        int count;
        int startLayer;
        int curLayer;
        int startLocation;
        int pos = 0;
        count = getComponentCount();
        startLocation = getIndexOf(c);
        if (startLocation == -1) return -1;
        startLayer = getLayer(c);
        for (i = startLocation - 1; i >= 0; i--) {
            curLayer = getLayer(getComponent(i));
            if (curLayer == startLayer) pos++; else return pos;
        }
        return pos;
    }
    
    public int highestLayer() {
        if (getComponentCount() > 0) return getLayer(getComponent(0));
        return 0;
    }
    
    public int lowestLayer() {
        int count = getComponentCount();
        if (count > 0) return getLayer(getComponent(count - 1));
        return 0;
    }
    
    public int getComponentCountInLayer(int layer) {
        int i;
        int count;
        int curLayer;
        int layerCount = 0;
        count = getComponentCount();
        for (i = 0; i < count; i++) {
            curLayer = getLayer(getComponent(i));
            if (curLayer == layer) {
                layerCount++;
            } else if (layerCount > 0 || curLayer < layer) {
                break;
            }
        }
        return layerCount;
    }
    
    public Component[] getComponentsInLayer(int layer) {
        int i;
        int count;
        int curLayer;
        int layerCount = 0;
        Component[] results;
        results = new Component[getComponentCountInLayer(layer)];
        count = getComponentCount();
        for (i = 0; i < count; i++) {
            curLayer = getLayer(getComponent(i));
            if (curLayer == layer) {
                results[layerCount++] = getComponent(i);
            } else if (layerCount > 0 || curLayer < layer) {
                break;
            }
        }
        return results;
    }
    
    public void paint(Graphics g) {
        if (isOpaque()) {
            Rectangle r = g.getClipBounds();
            Color c = getBackground();
            if (c == null) c = Color.lightGray;
            g.setColor(c);
            if (r != null) {
                g.fillRect(r.x, r.y, r.width, r.height);
            } else {
                g.fillRect(0, 0, getWidth(), getHeight());
            }
        }
        super.paint(g);
    }
    
    protected Hashtable getComponentToLayer() {
        if (componentToLayer == null) componentToLayer = new Hashtable(4);
        return componentToLayer;
    }
    
    protected Integer getObjectForLayer(int layer) {
        Integer layerObj;
        switch (layer) {
        case 0: 
            layerObj = DEFAULT_LAYER;
            break;
        
        case 100: 
            layerObj = PALETTE_LAYER;
            break;
        
        case 200: 
            layerObj = MODAL_LAYER;
            break;
        
        case 300: 
            layerObj = POPUP_LAYER;
            break;
        
        case 400: 
            layerObj = DRAG_LAYER;
            break;
        
        default: 
            layerObj = new Integer(layer);
        
        }
        return layerObj;
    }
    
    protected int insertIndexForLayer(int layer, int position) {
        return insertIndexForLayer(null, layer, position);
    }
    
    private int insertIndexForLayer(Component comp, int layer, int position) {
        int i;
        int count;
        int curLayer;
        int layerStart = -1;
        int layerEnd = -1;
        int componentCount = getComponentCount();
        ArrayList compList = new ArrayList(componentCount);
        for (int index = 0; index < componentCount; index++) {
            if (getComponent(index) != comp) {
                compList.add(getComponent(index));
            }
        }
        count = compList.size();
        for (i = 0; i < count; i++) {
            curLayer = getLayer((Component)compList.get(i));
            if (layerStart == -1 && curLayer == layer) {
                layerStart = i;
            }
            if (curLayer < layer) {
                if (i == 0) {
                    layerStart = 0;
                    layerEnd = 0;
                } else {
                    layerEnd = i;
                }
                break;
            }
        }
        if (layerStart == -1 && layerEnd == -1) return count;
        if (layerStart != -1 && layerEnd == -1) layerEnd = count;
        if (layerEnd != -1 && layerStart == -1) layerStart = layerEnd;
        if (position == -1) return layerEnd;
        if (position > -1 && layerStart + position <= layerEnd) return layerStart + position;
        return layerEnd;
    }
    
    protected String paramString() {
        String optimizedDrawingPossibleString = (optimizedDrawingPossible ? "true" : "false");
        return super.paramString() + ",optimizedDrawingPossible=" + optimizedDrawingPossibleString;
    }
    
    public AccessibleContext getAccessibleContext() {
        if (accessibleContext == null) {
            accessibleContext = new JLayeredPane$AccessibleJLayeredPane(this);
        }
        return accessibleContext;
    }
    {
    }
}
