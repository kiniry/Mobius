package java.util.concurrent;

import java.util.concurrent.locks.*;
import java.util.*;

final class ConcurrentHashMap$HashEntry {
    final Object key;
    final int hash;
    volatile Object value;
    final ConcurrentHashMap$HashEntry next;
    
    ConcurrentHashMap$HashEntry(Object key, int hash, ConcurrentHashMap$HashEntry next, Object value) {
        
        this.key = key;
        this.hash = hash;
        this.next = next;
        this.value = value;
    }
}
