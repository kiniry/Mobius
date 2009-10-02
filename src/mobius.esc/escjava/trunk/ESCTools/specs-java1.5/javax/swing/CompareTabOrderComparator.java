package javax.swing;

import java.awt.Component;
import java.util.Comparator;

final class CompareTabOrderComparator implements Comparator {
    private final DefaultFocusManager defaultFocusManager;
    
    CompareTabOrderComparator(DefaultFocusManager defaultFocusManager) {
        
        this.defaultFocusManager = defaultFocusManager;
    }
    
    public int compare(Object o1, Object o2) {
        if (o1 == o2) {
            return 0;
        }
        return (defaultFocusManager.compareTabOrder((Component)(Component)o1, (Component)(Component)o2)) ? -1 : 1;
    }
}
