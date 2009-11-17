package java.nio.charset;

import java.lang.ref.WeakReference;
import java.nio.*;
import java.util.Map;
import java.util.HashMap;

abstract class CoderResult$Cache {
    
    /*synthetic*/ static CoderResult access$200(CoderResult$Cache x0, int x1) {
        return x0.get(x1);
    }
    
    /*synthetic*/ CoderResult$Cache(java.nio.charset.CoderResult$1 x0) {
        this();
    }
    
    private CoderResult$Cache() {
        
    }
    private Map cache = null;
    
    protected abstract CoderResult create(int len);
    
    private synchronized CoderResult get(int len) {
        if (len <= 0) throw new IllegalArgumentException("Non-positive length");
        Integer k = new Integer(len);
        WeakReference w;
        CoderResult e = null;
        if (cache == null) {
            cache = new HashMap();
        } else if ((w = (WeakReference)(WeakReference)cache.get(k)) != null) {
            e = (CoderResult)(CoderResult)w.get();
        }
        if (e == null) {
            e = create(len);
            cache.put(k, new WeakReference(e));
        }
        return e;
    }
}
