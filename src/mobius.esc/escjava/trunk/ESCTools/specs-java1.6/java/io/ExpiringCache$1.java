package java.io;

import java.util.LinkedHashMap;

class ExpiringCache$1 extends LinkedHashMap {
    /*synthetic*/ final ExpiringCache this$0;
    
    ExpiringCache$1(/*synthetic*/ final ExpiringCache this$0) {
        this.this$0 = this$0;
        
    }
    
    protected boolean removeEldestEntry(Map$Entry eldest) {
        return size() > ExpiringCache.access$000(this$0);
    }
}
