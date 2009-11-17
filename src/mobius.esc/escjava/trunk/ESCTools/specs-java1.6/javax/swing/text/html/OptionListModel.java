package javax.swing.text.html;

import javax.swing.*;
import javax.swing.event.*;
import java.util.BitSet;
import java.io.Serializable;

class OptionListModel extends DefaultListModel implements ListSelectionModel, Serializable {
    
    OptionListModel() {
        
    }
    private static final int MIN = -1;
    private static final int MAX = Integer.MAX_VALUE;
    private int selectionMode = SINGLE_SELECTION;
    private int minIndex = MAX;
    private int maxIndex = MIN;
    private int anchorIndex = -1;
    private int leadIndex = -1;
    private int firstChangedIndex = MAX;
    private int lastChangedIndex = MIN;
    private boolean isAdjusting = false;
    private BitSet value = new BitSet(32);
    private BitSet initialValue = new BitSet(32);
    protected EventListenerList listenerList = new EventListenerList();
    protected boolean leadAnchorNotificationEnabled = true;
    
    public int getMinSelectionIndex() {
        return isSelectionEmpty() ? -1 : minIndex;
    }
    
    public int getMaxSelectionIndex() {
        return maxIndex;
    }
    
    public boolean getValueIsAdjusting() {
        return isAdjusting;
    }
    
    public int getSelectionMode() {
        return selectionMode;
    }
    
    public void setSelectionMode(int selectionMode) {
        switch (selectionMode) {
        case SINGLE_SELECTION: 
        
        case SINGLE_INTERVAL_SELECTION: 
        
        case MULTIPLE_INTERVAL_SELECTION: 
            this.selectionMode = selectionMode;
            break;
        
        default: 
            throw new IllegalArgumentException("invalid selectionMode");
        
        }
    }
    
    public boolean isSelectedIndex(int index) {
        return ((index < minIndex) || (index > maxIndex)) ? false : value.get(index);
    }
    
    public boolean isSelectionEmpty() {
        return (minIndex > maxIndex);
    }
    
    public void addListSelectionListener(ListSelectionListener l) {
        listenerList.add(ListSelectionListener.class, l);
    }
    
    public void removeListSelectionListener(ListSelectionListener l) {
        listenerList.remove(ListSelectionListener.class, l);
    }
    
    public ListSelectionListener[] getListSelectionListeners() {
        return (ListSelectionListener[])(ListSelectionListener[])listenerList.getListeners(ListSelectionListener.class);
    }
    
    protected void fireValueChanged(boolean isAdjusting) {
        fireValueChanged(getMinSelectionIndex(), getMaxSelectionIndex(), isAdjusting);
    }
    
    protected void fireValueChanged(int firstIndex, int lastIndex) {
        fireValueChanged(firstIndex, lastIndex, getValueIsAdjusting());
    }
    
    protected void fireValueChanged(int firstIndex, int lastIndex, boolean isAdjusting) {
        Object[] listeners = listenerList.getListenerList();
        ListSelectionEvent e = null;
        for (int i = listeners.length - 2; i >= 0; i -= 2) {
            if (listeners[i] == ListSelectionListener.class) {
                if (e == null) {
                    e = new ListSelectionEvent(this, firstIndex, lastIndex, isAdjusting);
                }
                ((ListSelectionListener)(ListSelectionListener)listeners[i + 1]).valueChanged(e);
            }
        }
    }
    
    private void fireValueChanged() {
        if (lastChangedIndex == MIN) {
            return;
        }
        int oldFirstChangedIndex = firstChangedIndex;
        int oldLastChangedIndex = lastChangedIndex;
        firstChangedIndex = MAX;
        lastChangedIndex = MIN;
        fireValueChanged(oldFirstChangedIndex, oldLastChangedIndex);
    }
    
    private void markAsDirty(int r) {
        firstChangedIndex = Math.min(firstChangedIndex, r);
        lastChangedIndex = Math.max(lastChangedIndex, r);
    }
    
    private void set(int r) {
        if (value.get(r)) {
            return;
        }
        value.set(r);
        Option option = (Option)(Option)get(r);
        option.setSelection(true);
        markAsDirty(r);
        minIndex = Math.min(minIndex, r);
        maxIndex = Math.max(maxIndex, r);
    }
    
    private void clear(int r) {
        if (!value.get(r)) {
            return;
        }
        value.clear(r);
        Option option = (Option)(Option)get(r);
        option.setSelection(false);
        markAsDirty(r);
        if (r == minIndex) {
            for (minIndex = minIndex + 1; minIndex <= maxIndex; minIndex++) {
                if (value.get(minIndex)) {
                    break;
                }
            }
        }
        if (r == maxIndex) {
            for (maxIndex = maxIndex - 1; minIndex <= maxIndex; maxIndex--) {
                if (value.get(maxIndex)) {
                    break;
                }
            }
        }
        if (isSelectionEmpty()) {
            minIndex = MAX;
            maxIndex = MIN;
        }
    }
    
    public void setLeadAnchorNotificationEnabled(boolean flag) {
        leadAnchorNotificationEnabled = flag;
    }
    
    public boolean isLeadAnchorNotificationEnabled() {
        return leadAnchorNotificationEnabled;
    }
    
    private void updateLeadAnchorIndices(int anchorIndex, int leadIndex) {
        if (leadAnchorNotificationEnabled) {
            if (this.anchorIndex != anchorIndex) {
                if (this.anchorIndex != -1) {
                    markAsDirty(this.anchorIndex);
                }
                markAsDirty(anchorIndex);
            }
            if (this.leadIndex != leadIndex) {
                if (this.leadIndex != -1) {
                    markAsDirty(this.leadIndex);
                }
                markAsDirty(leadIndex);
            }
        }
        this.anchorIndex = anchorIndex;
        this.leadIndex = leadIndex;
    }
    
    private boolean contains(int a, int b, int i) {
        return (i >= a) && (i <= b);
    }
    
    private void changeSelection(int clearMin, int clearMax, int setMin, int setMax, boolean clearFirst) {
        for (int i = Math.min(setMin, clearMin); i <= Math.max(setMax, clearMax); i++) {
            boolean shouldClear = contains(clearMin, clearMax, i);
            boolean shouldSet = contains(setMin, setMax, i);
            if (shouldSet && shouldClear) {
                if (clearFirst) {
                    shouldClear = false;
                } else {
                    shouldSet = false;
                }
            }
            if (shouldSet) {
                set(i);
            }
            if (shouldClear) {
                clear(i);
            }
        }
        fireValueChanged();
    }
    
    private void changeSelection(int clearMin, int clearMax, int setMin, int setMax) {
        changeSelection(clearMin, clearMax, setMin, setMax, true);
    }
    
    public void clearSelection() {
        removeSelectionInterval(minIndex, maxIndex);
    }
    
    public void setSelectionInterval(int index0, int index1) {
        if (index0 == -1 || index1 == -1) {
            return;
        }
        if (getSelectionMode() == SINGLE_SELECTION) {
            index0 = index1;
        }
        updateLeadAnchorIndices(index0, index1);
        int clearMin = minIndex;
        int clearMax = maxIndex;
        int setMin = Math.min(index0, index1);
        int setMax = Math.max(index0, index1);
        changeSelection(clearMin, clearMax, setMin, setMax);
    }
    
    public void addSelectionInterval(int index0, int index1) {
        if (index0 == -1 || index1 == -1) {
            return;
        }
        if (getSelectionMode() != MULTIPLE_INTERVAL_SELECTION) {
            setSelectionInterval(index0, index1);
            return;
        }
        updateLeadAnchorIndices(index0, index1);
        int clearMin = MAX;
        int clearMax = MIN;
        int setMin = Math.min(index0, index1);
        int setMax = Math.max(index0, index1);
        changeSelection(clearMin, clearMax, setMin, setMax);
    }
    
    public void removeSelectionInterval(int index0, int index1) {
        if (index0 == -1 || index1 == -1) {
            return;
        }
        updateLeadAnchorIndices(index0, index1);
        int clearMin = Math.min(index0, index1);
        int clearMax = Math.max(index0, index1);
        int setMin = MAX;
        int setMax = MIN;
        changeSelection(clearMin, clearMax, setMin, setMax);
    }
    
    private void setState(int index, boolean state) {
        if (state) {
            set(index);
        } else {
            clear(index);
        }
    }
    
    public void insertIndexInterval(int index, int length, boolean before) {
        int insMinIndex = (before) ? index : index + 1;
        int insMaxIndex = (insMinIndex + length) - 1;
        for (int i = maxIndex; i >= insMinIndex; i--) {
            setState(i + length, value.get(i));
        }
        boolean setInsertedValues = value.get(index);
        for (int i = insMinIndex; i <= insMaxIndex; i++) {
            setState(i, setInsertedValues);
        }
    }
    
    public void removeIndexInterval(int index0, int index1) {
        int rmMinIndex = Math.min(index0, index1);
        int rmMaxIndex = Math.max(index0, index1);
        int gapLength = (rmMaxIndex - rmMinIndex) + 1;
        for (int i = rmMinIndex; i <= maxIndex; i++) {
            setState(i, value.get(i + gapLength));
        }
    }
    
    public void setValueIsAdjusting(boolean isAdjusting) {
        if (isAdjusting != this.isAdjusting) {
            this.isAdjusting = isAdjusting;
            this.fireValueChanged(isAdjusting);
        }
    }
    
    public String toString() {
        String s = ((getValueIsAdjusting()) ? "~" : "=") + value.toString();
        return getClass().getName() + " " + Integer.toString(hashCode()) + " " + s;
    }
    
    public Object clone() throws CloneNotSupportedException {
        OptionListModel clone = (OptionListModel)(OptionListModel)super.clone();
        clone.value = (BitSet)(BitSet)value.clone();
        clone.listenerList = new EventListenerList();
        return clone;
    }
    
    public int getAnchorSelectionIndex() {
        return anchorIndex;
    }
    
    public int getLeadSelectionIndex() {
        return leadIndex;
    }
    
    public void setAnchorSelectionIndex(int anchorIndex) {
        this.anchorIndex = anchorIndex;
    }
    
    public void setLeadSelectionIndex(int leadIndex) {
        int anchorIndex = this.anchorIndex;
        if (getSelectionMode() == SINGLE_SELECTION) {
            anchorIndex = leadIndex;
        }
        int oldMin = Math.min(this.anchorIndex, this.leadIndex);
        ;
        int oldMax = Math.max(this.anchorIndex, this.leadIndex);
        ;
        int newMin = Math.min(anchorIndex, leadIndex);
        int newMax = Math.max(anchorIndex, leadIndex);
        if (value.get(this.anchorIndex)) {
            changeSelection(oldMin, oldMax, newMin, newMax);
        } else {
            changeSelection(newMin, newMax, oldMin, oldMax, false);
        }
        this.anchorIndex = anchorIndex;
        this.leadIndex = leadIndex;
    }
    
    public void setInitialSelection(int i) {
        if (initialValue.get(i)) {
            return;
        }
        if (selectionMode == SINGLE_SELECTION) {
            initialValue.and(new BitSet());
        }
        initialValue.set(i);
    }
    
    public BitSet getInitialSelection() {
        return initialValue;
    }
}
