package javax.swing;

public class ComponentInputMap extends InputMap {
    private JComponent component;
    
    public ComponentInputMap(JComponent component) {
        
        this.component = component;
        if (component == null) {
            throw new IllegalArgumentException("ComponentInputMaps must be associated with a non-null JComponent");
        }
    }
    
    public void setParent(InputMap map) {
        if (getParent() == map) {
            return;
        }
        if (map != null && (!(map instanceof ComponentInputMap) || ((ComponentInputMap)(ComponentInputMap)map).getComponent() != getComponent())) {
            throw new IllegalArgumentException("ComponentInputMaps must have a parent ComponentInputMap associated with the same component");
        }
        super.setParent(map);
        getComponent().componentInputMapChanged(this);
    }
    
    public JComponent getComponent() {
        return component;
    }
    
    public void put(KeyStroke keyStroke, Object actionMapKey) {
        super.put(keyStroke, actionMapKey);
        if (getComponent() != null) {
            getComponent().componentInputMapChanged(this);
        }
    }
    
    public void remove(KeyStroke key) {
        super.remove(key);
        if (getComponent() != null) {
            getComponent().componentInputMapChanged(this);
        }
    }
    
    public void clear() {
        int oldSize = size();
        super.clear();
        if (oldSize > 0 && getComponent() != null) {
            getComponent().componentInputMapChanged(this);
        }
    }
}
