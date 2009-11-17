package javax.swing;

public class SizeSequence {
    private static int[] emptyArray = new int[0];
    private int[] a;
    
    public SizeSequence() {
        
        a = emptyArray;
    }
    
    public SizeSequence(int numEntries) {
        this(numEntries, 0);
    }
    
    public SizeSequence(int numEntries, int value) {
        this();
        insertEntries(0, numEntries, value);
    }
    
    public SizeSequence(int[] sizes) {
        this();
        setSizes(sizes);
    }
    
    public void setSizes(int[] sizes) {
        if (a.length != sizes.length) {
            a = new int[sizes.length];
        }
        setSizes(0, a.length, sizes);
    }
    
    private int setSizes(int from, int to, int[] sizes) {
        if (to <= from) {
            return 0;
        }
        int m = (from + to) / 2;
        a[m] = sizes[m] + setSizes(from, m, sizes);
        return a[m] + setSizes(m + 1, to, sizes);
    }
    
    public int[] getSizes() {
        int n = a.length;
        int[] sizes = new int[n];
        getSizes(0, n, sizes);
        return sizes;
    }
    
    private int getSizes(int from, int to, int[] sizes) {
        if (to <= from) {
            return 0;
        }
        int m = (from + to) / 2;
        sizes[m] = a[m] - getSizes(from, m, sizes);
        return a[m] + getSizes(m + 1, to, sizes);
    }
    
    public int getPosition(int index) {
        return getPosition(0, a.length, index);
    }
    
    private int getPosition(int from, int to, int index) {
        if (to <= from) {
            return 0;
        }
        int m = (from + to) / 2;
        if (index <= m) {
            return getPosition(from, m, index);
        } else {
            return a[m] + getPosition(m + 1, to, index);
        }
    }
    
    public int getIndex(int position) {
        return getIndex(0, a.length, position);
    }
    
    private int getIndex(int from, int to, int position) {
        if (to <= from) {
            return from;
        }
        int m = (from + to) / 2;
        int pivot = a[m];
        if (position < pivot) {
            return getIndex(from, m, position);
        } else {
            return getIndex(m + 1, to, position - pivot);
        }
    }
    
    public int getSize(int index) {
        return getPosition(index + 1) - getPosition(index);
    }
    
    public void setSize(int index, int size) {
        changeSize(0, a.length, index, size - getSize(index));
    }
    
    private void changeSize(int from, int to, int index, int delta) {
        if (to <= from) {
            return;
        }
        int m = (from + to) / 2;
        if (index <= m) {
            a[m] += delta;
            changeSize(from, m, index, delta);
        } else {
            changeSize(m + 1, to, index, delta);
        }
    }
    
    public void insertEntries(int start, int length, int value) {
        int[] sizes = getSizes();
        int end = start + length;
        int n = a.length + length;
        a = new int[n];
        for (int i = 0; i < start; i++) {
            a[i] = sizes[i];
        }
        for (int i = start; i < end; i++) {
            a[i] = value;
        }
        for (int i = end; i < n; i++) {
            a[i] = sizes[i - length];
        }
        setSizes(a);
    }
    
    public void removeEntries(int start, int length) {
        int[] sizes = getSizes();
        int end = start + length;
        int n = a.length - length;
        a = new int[n];
        for (int i = 0; i < start; i++) {
            a[i] = sizes[i];
        }
        for (int i = start; i < n; i++) {
            a[i] = sizes[i + length];
        }
        setSizes(a);
    }
}
