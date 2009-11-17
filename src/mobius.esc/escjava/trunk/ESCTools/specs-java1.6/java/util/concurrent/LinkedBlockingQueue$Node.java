package java.util.concurrent;

import java.util.concurrent.atomic.*;
import java.util.concurrent.locks.*;
import java.util.*;

class LinkedBlockingQueue$Node {
    volatile Object item;
    LinkedBlockingQueue$Node next;
    
    LinkedBlockingQueue$Node(Object x) {
        
        item = x;
    }
}
