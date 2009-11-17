package javax.swing.text;

import java.io.Serializable;

public class TabSet implements Serializable {
    private TabStop[] tabs;
    private int hashCode = Integer.MAX_VALUE;
    
    public TabSet(TabStop[] tabs) {
        
        if (tabs != null) {
            int tabCount = tabs.length;
            this.tabs = new TabStop[tabCount];
            System.arraycopy(tabs, 0, this.tabs, 0, tabCount);
        } else this.tabs = null;
    }
    
    public int getTabCount() {
        return (tabs == null) ? 0 : tabs.length;
    }
    
    public TabStop getTab(int index) {
        int numTabs = getTabCount();
        if (index < 0 || index >= numTabs) throw new IllegalArgumentException(index + " is outside the range of tabs");
        return tabs[index];
    }
    
    public TabStop getTabAfter(float location) {
        int index = getTabIndexAfter(location);
        return (index == -1) ? null : tabs[index];
    }
    
    public int getTabIndex(TabStop tab) {
        for (int counter = getTabCount() - 1; counter >= 0; counter--) if (getTab(counter) == tab) return counter;
        return -1;
    }
    
    public int getTabIndexAfter(float location) {
        int current;
        int min;
        int max;
        min = 0;
        max = getTabCount();
        while (min != max) {
            current = (max - min) / 2 + min;
            if (location > tabs[current].getPosition()) {
                if (min == current) min = max; else min = current;
            } else {
                if (current == 0 || location > tabs[current - 1].getPosition()) return current;
                max = current;
            }
        }
        return -1;
    }
    
    public boolean equals(Object o) {
        if (o == this) {
            return true;
        }
        if (o instanceof TabSet) {
            TabSet ts = (TabSet)(TabSet)o;
            int count = getTabCount();
            if (ts.getTabCount() != count) {
                return false;
            }
            for (int i = 0; i < count; i++) {
                TabStop ts1 = getTab(i);
                TabStop ts2 = ts.getTab(i);
                if ((ts1 == null && ts2 != null) || (ts1 != null && !getTab(i).equals(ts.getTab(i)))) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }
    
    public int hashCode() {
        if (hashCode == Integer.MAX_VALUE) {
            hashCode = 0;
            int len = getTabCount();
            for (int i = 0; i < len; i++) {
                TabStop ts = getTab(i);
                hashCode ^= ts != null ? getTab(i).hashCode() : 0;
            }
            if (hashCode == Integer.MAX_VALUE) {
                hashCode -= 1;
            }
        }
        return hashCode;
    }
    
    public String toString() {
        int tabCount = getTabCount();
        StringBuffer buffer = new StringBuffer("[ ");
        for (int counter = 0; counter < tabCount; counter++) {
            if (counter > 0) buffer.append(" - ");
            buffer.append(getTab(counter).toString());
        }
        buffer.append(" ]");
        return buffer.toString();
    }
}
