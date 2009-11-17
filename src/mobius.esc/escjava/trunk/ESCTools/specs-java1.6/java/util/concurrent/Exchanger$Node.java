package java.util.concurrent;

import java.util.concurrent.atomic.*;

final class Exchanger$Node extends AtomicReference {
    public final Object item;
    public volatile Thread waiter;
    
    public Exchanger$Node(Object item) {
        
        this.item = item;
    }
}
