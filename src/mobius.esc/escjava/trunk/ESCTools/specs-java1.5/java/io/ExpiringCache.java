package java.io;

import java.util.Iterator;
import java.util.Map;
import java.util.Set;

class ExpiringCache {
    
    /*synthetic*/ static int access$000(ExpiringCache x0) {
        return x0.MAX_ENTRIES;
    }
    private long millisUntilExpiration;
    private Map map;
    private int queryCount;
    private int queryOverflow = 300;
    private int MAX_ENTRIES = 200;
    {
    }
    
    ExpiringCache() {
        this(30000);
    }
    
    ExpiringCache(long millisUntilExpiration) {
        
        this.millisUntilExpiration = millisUntilExpiration;
        map = new ExpiringCache$1(this);
    }
    
    synchronized String get(String key) {
        if (++queryCount >= queryOverflow) {
            cleanup();
        }
        ExpiringCache$Entry entry = entryFor(key);
        if (entry != null) {
            return entry.val();
        }
        return null;
    }
    
    synchronized void put(String key, String val) {
        if (++queryCount >= queryOverflow) {
            cleanup();
        }
        ExpiringCache$Entry entry = entryFor(key);
        if (entry != null) {
            entry.setTimestamp(System.currentTimeMillis());
            entry.setVal(val);
        } else {
            map.put(key, new ExpiringCache$Entry(System.currentTimeMillis(), val));
        }
    }
    
    synchronized void clear() {
        map.clear();
    }
    
    private ExpiringCache$Entry entryFor(String key) {
        ExpiringCache$Entry entry = (ExpiringCache$Entry)(ExpiringCache$Entry)map.get(key);
        if (entry != null) {
            long delta = System.currentTimeMillis() - entry.timestamp();
            if (delta < 0 || delta >= millisUntilExpiration) {
                map.remove(key);
                entry = null;
            }
        }
        return entry;
    }
    
    private void cleanup() {
        Set keySet = map.keySet();
        String[] keys = new String[keySet.size()];
        int i = 0;
        for (Iterator iter = keySet.iterator(); iter.hasNext(); ) {
            String key = (String)(String)iter.next();
            keys[i++] = key;
        }
        for (int j = 0; j < keys.length; j++) {
            entryFor(keys[j]);
        }
        queryCount = 0;
    }
}
