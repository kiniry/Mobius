package java.util.prefs;

import java.util.*;
import java.io.*;
import java.security.AccessController;
import java.lang.Integer;
import java.lang.Long;
import java.lang.Float;
import java.lang.Double;

public abstract class AbstractPreferences extends Preferences {
    
    /*synthetic*/ static List access$100() {
        return eventQueue;
    }
    
    /*synthetic*/ static AbstractPreferences access$000(AbstractPreferences x0) {
        return x0.root;
    }
    private final String name;
    private final String absolutePath;
    final AbstractPreferences parent;
    private final AbstractPreferences root;
    protected boolean newNode = false;
    private Map kidCache = new HashMap();
    private boolean removed = false;
    private PreferenceChangeListener[] prefListeners = new PreferenceChangeListener[0];
    private NodeChangeListener[] nodeListeners = new NodeChangeListener[0];
    protected final Object lock = new Object();
    
    protected AbstractPreferences(AbstractPreferences parent, String name) {
        
        if (parent == null) {
            if (!name.equals("")) throw new IllegalArgumentException("Root name \'" + name + "\' must be \"\"");
            this.absolutePath = "/";
            root = this;
        } else {
            if (name.indexOf('/') != -1) throw new IllegalArgumentException("Name \'" + name + "\' contains \'/\'");
            if (name.equals("")) throw new IllegalArgumentException("Illegal name: empty string");
            root = parent.root;
            absolutePath = (parent == root ? "/" + name : parent.absolutePath() + "/" + name);
        }
        this.name = name;
        this.parent = parent;
    }
    
    public void put(String key, String value) {
        if (key == null || value == null) throw new NullPointerException();
        if (key.length() > MAX_KEY_LENGTH) throw new IllegalArgumentException("Key too long: " + key);
        if (value.length() > MAX_VALUE_LENGTH) throw new IllegalArgumentException("Value too long: " + value);
        synchronized (lock) {
            if (removed) throw new IllegalStateException("Node has been removed.");
            putSpi(key, value);
            enqueuePreferenceChangeEvent(key, value);
        }
    }
    
    public String get(String key, String def) {
        if (key == null) throw new NullPointerException("Null key");
        synchronized (lock) {
            if (removed) throw new IllegalStateException("Node has been removed.");
            String result = null;
            try {
                result = getSpi(key);
            } catch (Exception e) {
            }
            return (result == null ? def : result);
        }
    }
    
    public void remove(String key) {
        synchronized (lock) {
            if (removed) throw new IllegalStateException("Node has been removed.");
            removeSpi(key);
            enqueuePreferenceChangeEvent(key, null);
        }
    }
    
    public void clear() throws BackingStoreException {
        synchronized (lock) {
            String[] keys = keys();
            for (int i = 0; i < keys.length; i++) remove(keys[i]);
        }
    }
    
    public void putInt(String key, int value) {
        put(key, Integer.toString(value));
    }
    
    public int getInt(String key, int def) {
        int result = def;
        try {
            String value = get(key, null);
            if (value != null) result = Integer.parseInt(value);
        } catch (NumberFormatException e) {
        }
        return result;
    }
    
    public void putLong(String key, long value) {
        put(key, Long.toString(value));
    }
    
    public long getLong(String key, long def) {
        long result = def;
        try {
            String value = get(key, null);
            if (value != null) result = Long.parseLong(value);
        } catch (NumberFormatException e) {
        }
        return result;
    }
    
    public void putBoolean(String key, boolean value) {
        put(key, String.valueOf(value));
    }
    
    public boolean getBoolean(String key, boolean def) {
        boolean result = def;
        String value = get(key, null);
        if (value != null) {
            if (value.equalsIgnoreCase("true")) result = true; else if (value.equalsIgnoreCase("false")) result = false;
        }
        return result;
    }
    
    public void putFloat(String key, float value) {
        put(key, Float.toString(value));
    }
    
    public float getFloat(String key, float def) {
        float result = def;
        try {
            String value = get(key, null);
            if (value != null) result = Float.parseFloat(value);
        } catch (NumberFormatException e) {
        }
        return result;
    }
    
    public void putDouble(String key, double value) {
        put(key, Double.toString(value));
    }
    
    public double getDouble(String key, double def) {
        double result = def;
        try {
            String value = get(key, null);
            if (value != null) result = Double.parseDouble(value);
        } catch (NumberFormatException e) {
        }
        return result;
    }
    
    public void putByteArray(String key, byte[] value) {
        put(key, Base64.byteArrayToBase64(value));
    }
    
    public byte[] getByteArray(String key, byte[] def) {
        byte[] result = def;
        String value = get(key, null);
        try {
            if (value != null) result = Base64.base64ToByteArray(value);
        } catch (RuntimeException e) {
        }
        return result;
    }
    
    public String[] keys() throws BackingStoreException {
        synchronized (lock) {
            if (removed) throw new IllegalStateException("Node has been removed.");
            return keysSpi();
        }
    }
    
    public String[] childrenNames() throws BackingStoreException {
        synchronized (lock) {
            if (removed) throw new IllegalStateException("Node has been removed.");
            Set s = new TreeSet(kidCache.keySet());
            String[] kids = childrenNamesSpi();
            for (int i = 0; i < kids.length; i++) s.add(kids[i]);
            return (String[])(String[])s.toArray(EMPTY_STRING_ARRAY);
        }
    }
    private static final String[] EMPTY_STRING_ARRAY = new String[0];
    
    protected final AbstractPreferences[] cachedChildren() {
        return (AbstractPreferences[])(AbstractPreferences[])kidCache.values().toArray(EMPTY_ABSTRACT_PREFS_ARRAY);
    }
    private static final AbstractPreferences[] EMPTY_ABSTRACT_PREFS_ARRAY = new AbstractPreferences[0];
    
    public Preferences parent() {
        synchronized (lock) {
            if (removed) throw new IllegalStateException("Node has been removed.");
            return parent;
        }
    }
    
    public Preferences node(String path) {
        synchronized (lock) {
            if (removed) throw new IllegalStateException("Node has been removed.");
            if (path.equals("")) return this;
            if (path.equals("/")) return root;
            if (path.charAt(0) != '/') return node(new StringTokenizer(path, "/", true));
        }
        return root.node(new StringTokenizer(path.substring(1), "/", true));
    }
    
    private Preferences node(StringTokenizer path) {
        String token = path.nextToken();
        if (token.equals("/")) throw new IllegalArgumentException("Consecutive slashes in path");
        synchronized (lock) {
            AbstractPreferences child = (AbstractPreferences)(AbstractPreferences)kidCache.get(token);
            if (child == null) {
                if (token.length() > MAX_NAME_LENGTH) throw new IllegalArgumentException("Node name " + token + " too long");
                child = childSpi(token);
                if (child.newNode) enqueueNodeAddedEvent(child);
                kidCache.put(token, child);
            }
            if (!path.hasMoreTokens()) return child;
            path.nextToken();
            if (!path.hasMoreTokens()) throw new IllegalArgumentException("Path ends with slash");
            return child.node(path);
        }
    }
    
    public boolean nodeExists(String path) throws BackingStoreException {
        synchronized (lock) {
            if (path.equals("")) return !removed;
            if (removed) throw new IllegalStateException("Node has been removed.");
            if (path.equals("/")) return true;
            if (path.charAt(0) != '/') return nodeExists(new StringTokenizer(path, "/", true));
        }
        return root.nodeExists(new StringTokenizer(path.substring(1), "/", true));
    }
    
    private boolean nodeExists(StringTokenizer path) throws BackingStoreException {
        String token = path.nextToken();
        if (token.equals("/")) throw new IllegalArgumentException("Consecutive slashes in path");
        synchronized (lock) {
            AbstractPreferences child = (AbstractPreferences)(AbstractPreferences)kidCache.get(token);
            if (child == null) child = getChild(token);
            if (child == null) return false;
            if (!path.hasMoreTokens()) return true;
            path.nextToken();
            if (!path.hasMoreTokens()) throw new IllegalArgumentException("Path ends with slash");
            return child.nodeExists(path);
        }
    }
    
    public void removeNode() throws BackingStoreException {
        if (this == root) throw new UnsupportedOperationException("Can\'t remove the root!");
        synchronized (parent.lock) {
            removeNode2();
            parent.kidCache.remove(name);
        }
    }
    
    private void removeNode2() throws BackingStoreException {
        synchronized (lock) {
            if (removed) throw new IllegalStateException("Node already removed.");
            String[] kidNames = childrenNamesSpi();
            for (int i = 0; i < kidNames.length; i++) if (!kidCache.containsKey(kidNames[i])) kidCache.put(kidNames[i], childSpi(kidNames[i]));
            for (Iterator i = kidCache.values().iterator(); i.hasNext(); ) ((AbstractPreferences)(AbstractPreferences)i.next()).removeNode2();
            kidCache.clear();
            removeNodeSpi();
            removed = true;
            parent.enqueueNodeRemovedEvent(this);
        }
    }
    
    public String name() {
        return name;
    }
    
    public String absolutePath() {
        return absolutePath;
    }
    
    public boolean isUserNode() {
        Boolean result = (Boolean)(Boolean)AccessController.doPrivileged(new AbstractPreferences$1(this));
        return result.booleanValue();
    }
    
    public void addPreferenceChangeListener(PreferenceChangeListener pcl) {
        if (pcl == null) throw new NullPointerException("Change listener is null.");
        synchronized (lock) {
            if (removed) throw new IllegalStateException("Node has been removed.");
            PreferenceChangeListener[] old = prefListeners;
            prefListeners = new PreferenceChangeListener[old.length + 1];
            System.arraycopy(old, 0, prefListeners, 0, old.length);
            prefListeners[old.length] = pcl;
        }
        startEventDispatchThreadIfNecessary();
    }
    
    public void removePreferenceChangeListener(PreferenceChangeListener pcl) {
        synchronized (lock) {
            if (removed) throw new IllegalStateException("Node has been removed.");
            if ((prefListeners == null) || (prefListeners.length == 0)) throw new IllegalArgumentException("Listener not registered.");
            PreferenceChangeListener[] newPl = new PreferenceChangeListener[prefListeners.length - 1];
            int i = 0;
            while (i < newPl.length && prefListeners[i] != pcl) newPl[i] = prefListeners[i++];
            if (i == newPl.length && prefListeners[i] != pcl) throw new IllegalArgumentException("Listener not registered.");
            while (i < newPl.length) newPl[i] = prefListeners[++i];
            prefListeners = newPl;
        }
    }
    
    public void addNodeChangeListener(NodeChangeListener ncl) {
        if (ncl == null) throw new NullPointerException("Change listener is null.");
        synchronized (lock) {
            if (removed) throw new IllegalStateException("Node has been removed.");
            if (nodeListeners == null) {
                nodeListeners = new NodeChangeListener[1];
                nodeListeners[0] = ncl;
            } else {
                NodeChangeListener[] old = nodeListeners;
                nodeListeners = new NodeChangeListener[old.length + 1];
                System.arraycopy(old, 0, nodeListeners, 0, old.length);
                nodeListeners[old.length] = ncl;
            }
        }
        startEventDispatchThreadIfNecessary();
    }
    
    public void removeNodeChangeListener(NodeChangeListener ncl) {
        synchronized (lock) {
            if (removed) throw new IllegalStateException("Node has been removed.");
            if ((nodeListeners == null) || (nodeListeners.length == 0)) throw new IllegalArgumentException("Listener not registered.");
            NodeChangeListener[] newNl = new NodeChangeListener[nodeListeners.length - 1];
            int i = 0;
            while (i < nodeListeners.length && nodeListeners[i] != ncl) newNl[i] = nodeListeners[i++];
            if (i == nodeListeners.length) throw new IllegalArgumentException("Listener not registered.");
            while (i < newNl.length) newNl[i] = nodeListeners[++i];
            nodeListeners = newNl;
        }
    }
    
    protected abstract void putSpi(String key, String value);
    
    protected abstract String getSpi(String key);
    
    protected abstract void removeSpi(String key);
    
    protected abstract void removeNodeSpi() throws BackingStoreException;
    
    protected abstract String[] keysSpi() throws BackingStoreException;
    
    protected abstract String[] childrenNamesSpi() throws BackingStoreException;
    
    protected AbstractPreferences getChild(String nodeName) throws BackingStoreException {
        synchronized (lock) {
            String[] kidNames = childrenNames();
            for (int i = 0; i < kidNames.length; i++) if (kidNames[i].equals(nodeName)) return childSpi(kidNames[i]);
        }
        return null;
    }
    
    protected abstract AbstractPreferences childSpi(String name);
    
    public String toString() {
        return (this.isUserNode() ? "User" : "System") + " Preference Node: " + this.absolutePath();
    }
    
    public void sync() throws BackingStoreException {
        sync2();
    }
    
    private void sync2() throws BackingStoreException {
        AbstractPreferences[] cachedKids;
        synchronized (lock) {
            if (removed) throw new IllegalStateException("Node has been removed");
            syncSpi();
            cachedKids = cachedChildren();
        }
        for (int i = 0; i < cachedKids.length; i++) cachedKids[i].sync2();
    }
    
    protected abstract void syncSpi() throws BackingStoreException;
    
    public void flush() throws BackingStoreException {
        flush2();
    }
    
    private void flush2() throws BackingStoreException {
        AbstractPreferences[] cachedKids;
        synchronized (lock) {
            flushSpi();
            if (removed) return;
            cachedKids = cachedChildren();
        }
        for (int i = 0; i < cachedKids.length; i++) cachedKids[i].flush2();
    }
    
    protected abstract void flushSpi() throws BackingStoreException;
    
    protected boolean isRemoved() {
        synchronized (lock) {
            return removed;
        }
    }
    private static final List eventQueue = new LinkedList();
    {
    }
    {
    }
    {
    }
    private static Thread eventDispatchThread = null;
    
    private static synchronized void startEventDispatchThreadIfNecessary() {
        if (eventDispatchThread == null) {
            eventDispatchThread = new AbstractPreferences$EventDispatchThread(null);
            eventDispatchThread.setDaemon(true);
            eventDispatchThread.start();
        }
    }
    
    PreferenceChangeListener[] prefListeners() {
        synchronized (lock) {
            return prefListeners;
        }
    }
    
    NodeChangeListener[] nodeListeners() {
        synchronized (lock) {
            return nodeListeners;
        }
    }
    
    private void enqueuePreferenceChangeEvent(String key, String newValue) {
        if (prefListeners.length != 0) {
            synchronized (eventQueue) {
                eventQueue.add(new PreferenceChangeEvent(this, key, newValue));
                eventQueue.notify();
            }
        }
    }
    
    private void enqueueNodeAddedEvent(Preferences child) {
        if (nodeListeners.length != 0) {
            synchronized (eventQueue) {
                eventQueue.add(new AbstractPreferences$NodeAddedEvent(this, this, child));
                eventQueue.notify();
            }
        }
    }
    
    private void enqueueNodeRemovedEvent(Preferences child) {
        if (nodeListeners.length != 0) {
            synchronized (eventQueue) {
                eventQueue.add(new AbstractPreferences$NodeRemovedEvent(this, this, child));
                eventQueue.notify();
            }
        }
    }
    
    public void exportNode(OutputStream os) throws IOException, BackingStoreException {
        XmlSupport.export(os, this, false);
    }
    
    public void exportSubtree(OutputStream os) throws IOException, BackingStoreException {
        XmlSupport.export(os, this, true);
    }
}
