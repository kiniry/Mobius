package java.util.concurrent;

import java.util.*;

public interface Delayed extends Comparable {
    
    long getDelay(TimeUnit unit);
}
