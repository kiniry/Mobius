package java.util.concurrent;

import java.util.*;
import java.util.concurrent.locks.*;
import java.util.concurrent.atomic.*;

final class Semaphore$NonfairSync extends Semaphore$Sync {
    
    Semaphore$NonfairSync(int permits) {
        super(permits);
    }
    
    protected int tryAcquireShared(int acquires) {
        return nonfairTryAcquireShared(acquires);
    }
}
