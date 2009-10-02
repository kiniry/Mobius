package javax.swing.plaf.basic;

import java.lang.reflect.*;
import javax.swing.*;
import javax.swing.plaf.*;

class LazyActionMap extends ActionMapUIResource {
    /*synthetic*/ static final boolean $assertionsDisabled = !LazyActionMap.class.desiredAssertionStatus();
    private transient Object _loader;
    
    static void installLazyActionMap(JComponent c, Class loaderClass, String defaultsKey) {
        ActionMap map = (ActionMap)(ActionMap)UIManager.get(defaultsKey);
        if (map == null) {
            map = new LazyActionMap(loaderClass);
            UIManager.getLookAndFeelDefaults().put(defaultsKey, map);
        }
        SwingUtilities.replaceUIActionMap(c, map);
    }
    
    static ActionMap getActionMap(Class loaderClass, String defaultsKey) {
        ActionMap map = (ActionMap)(ActionMap)UIManager.get(defaultsKey);
        if (map == null) {
            map = new LazyActionMap(loaderClass);
            UIManager.getLookAndFeelDefaults().put(defaultsKey, map);
        }
        return map;
    }
    
    private LazyActionMap(Class loader) {
        
        _loader = loader;
    }
    
    public void put(Action action) {
        put(action.getValue(Action.NAME), action);
    }
    
    public void put(Object key, Action action) {
        loadIfNecessary();
        super.put(key, action);
    }
    
    public Action get(Object key) {
        loadIfNecessary();
        return super.get(key);
    }
    
    public void remove(Object key) {
        loadIfNecessary();
        super.remove(key);
    }
    
    public void clear() {
        loadIfNecessary();
        super.clear();
    }
    
    public Object[] keys() {
        loadIfNecessary();
        return super.keys();
    }
    
    public int size() {
        loadIfNecessary();
        return super.size();
    }
    
    public Object[] allKeys() {
        loadIfNecessary();
        return super.allKeys();
    }
    
    public void setParent(ActionMap map) {
        loadIfNecessary();
        super.setParent(map);
    }
    
    private void loadIfNecessary() {
        if (_loader != null) {
            Object loader = _loader;
            _loader = null;
            Class klass = (Class)(Class)loader;
            try {
                Method method = klass.getDeclaredMethod("loadActionMap", new Class[]{LazyActionMap.class});
                method.invoke(klass, new Object[]{this});
            } catch (NoSuchMethodException nsme) {
                if (!$assertionsDisabled) throw new AssertionError("LazyActionMap unable to load actions " + klass);
            } catch (IllegalAccessException iae) {
                if (!$assertionsDisabled) throw new AssertionError("LazyActionMap unable to load actions " + iae);
            } catch (InvocationTargetException ite) {
                if (!$assertionsDisabled) throw new AssertionError("LazyActionMap unable to load actions " + ite);
            } catch (IllegalArgumentException iae) {
                if (!$assertionsDisabled) throw new AssertionError("LazyActionMap unable to load actions " + iae);
            }
        }
    }
}
