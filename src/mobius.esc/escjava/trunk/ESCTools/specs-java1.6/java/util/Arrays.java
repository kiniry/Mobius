package java.util;

import java.lang.reflect.*;

public class Arrays {
    
    private Arrays() {
        
    }
    
    public static void sort(long[] a) {
        sort1(a, 0, a.length);
    }
    
    public static void sort(long[] a, int fromIndex, int toIndex) {
        rangeCheck(a.length, fromIndex, toIndex);
        sort1(a, fromIndex, toIndex - fromIndex);
    }
    
    public static void sort(int[] a) {
        sort1(a, 0, a.length);
    }
    
    public static void sort(int[] a, int fromIndex, int toIndex) {
        rangeCheck(a.length, fromIndex, toIndex);
        sort1(a, fromIndex, toIndex - fromIndex);
    }
    
    public static void sort(short[] a) {
        sort1(a, 0, a.length);
    }
    
    public static void sort(short[] a, int fromIndex, int toIndex) {
        rangeCheck(a.length, fromIndex, toIndex);
        sort1(a, fromIndex, toIndex - fromIndex);
    }
    
    public static void sort(char[] a) {
        sort1(a, 0, a.length);
    }
    
    public static void sort(char[] a, int fromIndex, int toIndex) {
        rangeCheck(a.length, fromIndex, toIndex);
        sort1(a, fromIndex, toIndex - fromIndex);
    }
    
    public static void sort(byte[] a) {
        sort1(a, 0, a.length);
    }
    
    public static void sort(byte[] a, int fromIndex, int toIndex) {
        rangeCheck(a.length, fromIndex, toIndex);
        sort1(a, fromIndex, toIndex - fromIndex);
    }
    
    public static void sort(double[] a) {
        sort2(a, 0, a.length);
    }
    
    public static void sort(double[] a, int fromIndex, int toIndex) {
        rangeCheck(a.length, fromIndex, toIndex);
        sort2(a, fromIndex, toIndex);
    }
    
    public static void sort(float[] a) {
        sort2(a, 0, a.length);
    }
    
    public static void sort(float[] a, int fromIndex, int toIndex) {
        rangeCheck(a.length, fromIndex, toIndex);
        sort2(a, fromIndex, toIndex);
    }
    
    private static void sort2(double[] a, int fromIndex, int toIndex) {
        final long NEG_ZERO_BITS = Double.doubleToLongBits(-0.0);
        int numNegZeros = 0;
        int i = fromIndex;
        int n = toIndex;
        while (i < n) {
            if (a[i] != a[i]) {
                double swap = a[i];
                a[i] = a[--n];
                a[n] = swap;
            } else {
                if (a[i] == 0 && Double.doubleToLongBits(a[i]) == NEG_ZERO_BITS) {
                    a[i] = 0.0;
                    numNegZeros++;
                }
                i++;
            }
        }
        sort1(a, fromIndex, n - fromIndex);
        if (numNegZeros != 0) {
            int j = binarySearch(a, 0.0, fromIndex, n - 1);
            do {
                j--;
            }             while (j >= 0 && a[j] == 0.0);
            for (int k = 0; k < numNegZeros; k++) a[++j] = -0.0;
        }
    }
    
    private static void sort2(float[] a, int fromIndex, int toIndex) {
        final int NEG_ZERO_BITS = Float.floatToIntBits(-0.0F);
        int numNegZeros = 0;
        int i = fromIndex;
        int n = toIndex;
        while (i < n) {
            if (a[i] != a[i]) {
                float swap = a[i];
                a[i] = a[--n];
                a[n] = swap;
            } else {
                if (a[i] == 0 && Float.floatToIntBits(a[i]) == NEG_ZERO_BITS) {
                    a[i] = 0.0F;
                    numNegZeros++;
                }
                i++;
            }
        }
        sort1(a, fromIndex, n - fromIndex);
        if (numNegZeros != 0) {
            int j = binarySearch(a, 0.0F, fromIndex, n - 1);
            do {
                j--;
            }             while (j >= 0 && a[j] == 0.0F);
            for (int k = 0; k < numNegZeros; k++) a[++j] = -0.0F;
        }
    }
    
    private static void sort1(long[] x, int off, int len) {
        if (len < 7) {
            for (int i = off; i < len + off; i++) for (int j = i; j > off && x[j - 1] > x[j]; j--) swap(x, j, j - 1);
            return;
        }
        int m = off + (len >> 1);
        if (len > 7) {
            int l = off;
            int n = off + len - 1;
            if (len > 40) {
                int s = len / 8;
                l = med3(x, l, l + s, l + 2 * s);
                m = med3(x, m - s, m, m + s);
                n = med3(x, n - 2 * s, n - s, n);
            }
            m = med3(x, l, m, n);
        }
        long v = x[m];
        int a = off;
        int b = a;
        int c = off + len - 1;
        int d = c;
        while (true) {
            while (b <= c && x[b] <= v) {
                if (x[b] == v) swap(x, a++, b);
                b++;
            }
            while (c >= b && x[c] >= v) {
                if (x[c] == v) swap(x, c, d--);
                c--;
            }
            if (b > c) break;
            swap(x, b++, c--);
        }
        int s;
        int n = off + len;
        s = Math.min(a - off, b - a);
        vecswap(x, off, b - s, s);
        s = Math.min(d - c, n - d - 1);
        vecswap(x, b, n - s, s);
        if ((s = b - a) > 1) sort1(x, off, s);
        if ((s = d - c) > 1) sort1(x, n - s, s);
    }
    
    private static void swap(long[] x, int a, int b) {
        long t = x[a];
        x[a] = x[b];
        x[b] = t;
    }
    
    private static void vecswap(long[] x, int a, int b, int n) {
        for (int i = 0; i < n; i++, a++, b++) swap(x, a, b);
    }
    
    private static int med3(long[] x, int a, int b, int c) {
        return (x[a] < x[b] ? (x[b] < x[c] ? b : x[a] < x[c] ? c : a) : (x[b] > x[c] ? b : x[a] > x[c] ? c : a));
    }
    
    private static void sort1(int[] x, int off, int len) {
        if (len < 7) {
            for (int i = off; i < len + off; i++) for (int j = i; j > off && x[j - 1] > x[j]; j--) swap(x, j, j - 1);
            return;
        }
        int m = off + (len >> 1);
        if (len > 7) {
            int l = off;
            int n = off + len - 1;
            if (len > 40) {
                int s = len / 8;
                l = med3(x, l, l + s, l + 2 * s);
                m = med3(x, m - s, m, m + s);
                n = med3(x, n - 2 * s, n - s, n);
            }
            m = med3(x, l, m, n);
        }
        int v = x[m];
        int a = off;
        int b = a;
        int c = off + len - 1;
        int d = c;
        while (true) {
            while (b <= c && x[b] <= v) {
                if (x[b] == v) swap(x, a++, b);
                b++;
            }
            while (c >= b && x[c] >= v) {
                if (x[c] == v) swap(x, c, d--);
                c--;
            }
            if (b > c) break;
            swap(x, b++, c--);
        }
        int s;
        int n = off + len;
        s = Math.min(a - off, b - a);
        vecswap(x, off, b - s, s);
        s = Math.min(d - c, n - d - 1);
        vecswap(x, b, n - s, s);
        if ((s = b - a) > 1) sort1(x, off, s);
        if ((s = d - c) > 1) sort1(x, n - s, s);
    }
    
    private static void swap(int[] x, int a, int b) {
        int t = x[a];
        x[a] = x[b];
        x[b] = t;
    }
    
    private static void vecswap(int[] x, int a, int b, int n) {
        for (int i = 0; i < n; i++, a++, b++) swap(x, a, b);
    }
    
    private static int med3(int[] x, int a, int b, int c) {
        return (x[a] < x[b] ? (x[b] < x[c] ? b : x[a] < x[c] ? c : a) : (x[b] > x[c] ? b : x[a] > x[c] ? c : a));
    }
    
    private static void sort1(short[] x, int off, int len) {
        if (len < 7) {
            for (int i = off; i < len + off; i++) for (int j = i; j > off && x[j - 1] > x[j]; j--) swap(x, j, j - 1);
            return;
        }
        int m = off + (len >> 1);
        if (len > 7) {
            int l = off;
            int n = off + len - 1;
            if (len > 40) {
                int s = len / 8;
                l = med3(x, l, l + s, l + 2 * s);
                m = med3(x, m - s, m, m + s);
                n = med3(x, n - 2 * s, n - s, n);
            }
            m = med3(x, l, m, n);
        }
        short v = x[m];
        int a = off;
        int b = a;
        int c = off + len - 1;
        int d = c;
        while (true) {
            while (b <= c && x[b] <= v) {
                if (x[b] == v) swap(x, a++, b);
                b++;
            }
            while (c >= b && x[c] >= v) {
                if (x[c] == v) swap(x, c, d--);
                c--;
            }
            if (b > c) break;
            swap(x, b++, c--);
        }
        int s;
        int n = off + len;
        s = Math.min(a - off, b - a);
        vecswap(x, off, b - s, s);
        s = Math.min(d - c, n - d - 1);
        vecswap(x, b, n - s, s);
        if ((s = b - a) > 1) sort1(x, off, s);
        if ((s = d - c) > 1) sort1(x, n - s, s);
    }
    
    private static void swap(short[] x, int a, int b) {
        short t = x[a];
        x[a] = x[b];
        x[b] = t;
    }
    
    private static void vecswap(short[] x, int a, int b, int n) {
        for (int i = 0; i < n; i++, a++, b++) swap(x, a, b);
    }
    
    private static int med3(short[] x, int a, int b, int c) {
        return (x[a] < x[b] ? (x[b] < x[c] ? b : x[a] < x[c] ? c : a) : (x[b] > x[c] ? b : x[a] > x[c] ? c : a));
    }
    
    private static void sort1(char[] x, int off, int len) {
        if (len < 7) {
            for (int i = off; i < len + off; i++) for (int j = i; j > off && x[j - 1] > x[j]; j--) swap(x, j, j - 1);
            return;
        }
        int m = off + (len >> 1);
        if (len > 7) {
            int l = off;
            int n = off + len - 1;
            if (len > 40) {
                int s = len / 8;
                l = med3(x, l, l + s, l + 2 * s);
                m = med3(x, m - s, m, m + s);
                n = med3(x, n - 2 * s, n - s, n);
            }
            m = med3(x, l, m, n);
        }
        char v = x[m];
        int a = off;
        int b = a;
        int c = off + len - 1;
        int d = c;
        while (true) {
            while (b <= c && x[b] <= v) {
                if (x[b] == v) swap(x, a++, b);
                b++;
            }
            while (c >= b && x[c] >= v) {
                if (x[c] == v) swap(x, c, d--);
                c--;
            }
            if (b > c) break;
            swap(x, b++, c--);
        }
        int s;
        int n = off + len;
        s = Math.min(a - off, b - a);
        vecswap(x, off, b - s, s);
        s = Math.min(d - c, n - d - 1);
        vecswap(x, b, n - s, s);
        if ((s = b - a) > 1) sort1(x, off, s);
        if ((s = d - c) > 1) sort1(x, n - s, s);
    }
    
    private static void swap(char[] x, int a, int b) {
        char t = x[a];
        x[a] = x[b];
        x[b] = t;
    }
    
    private static void vecswap(char[] x, int a, int b, int n) {
        for (int i = 0; i < n; i++, a++, b++) swap(x, a, b);
    }
    
    private static int med3(char[] x, int a, int b, int c) {
        return (x[a] < x[b] ? (x[b] < x[c] ? b : x[a] < x[c] ? c : a) : (x[b] > x[c] ? b : x[a] > x[c] ? c : a));
    }
    
    private static void sort1(byte[] x, int off, int len) {
        if (len < 7) {
            for (int i = off; i < len + off; i++) for (int j = i; j > off && x[j - 1] > x[j]; j--) swap(x, j, j - 1);
            return;
        }
        int m = off + (len >> 1);
        if (len > 7) {
            int l = off;
            int n = off + len - 1;
            if (len > 40) {
                int s = len / 8;
                l = med3(x, l, l + s, l + 2 * s);
                m = med3(x, m - s, m, m + s);
                n = med3(x, n - 2 * s, n - s, n);
            }
            m = med3(x, l, m, n);
        }
        byte v = x[m];
        int a = off;
        int b = a;
        int c = off + len - 1;
        int d = c;
        while (true) {
            while (b <= c && x[b] <= v) {
                if (x[b] == v) swap(x, a++, b);
                b++;
            }
            while (c >= b && x[c] >= v) {
                if (x[c] == v) swap(x, c, d--);
                c--;
            }
            if (b > c) break;
            swap(x, b++, c--);
        }
        int s;
        int n = off + len;
        s = Math.min(a - off, b - a);
        vecswap(x, off, b - s, s);
        s = Math.min(d - c, n - d - 1);
        vecswap(x, b, n - s, s);
        if ((s = b - a) > 1) sort1(x, off, s);
        if ((s = d - c) > 1) sort1(x, n - s, s);
    }
    
    private static void swap(byte[] x, int a, int b) {
        byte t = x[a];
        x[a] = x[b];
        x[b] = t;
    }
    
    private static void vecswap(byte[] x, int a, int b, int n) {
        for (int i = 0; i < n; i++, a++, b++) swap(x, a, b);
    }
    
    private static int med3(byte[] x, int a, int b, int c) {
        return (x[a] < x[b] ? (x[b] < x[c] ? b : x[a] < x[c] ? c : a) : (x[b] > x[c] ? b : x[a] > x[c] ? c : a));
    }
    
    private static void sort1(double[] x, int off, int len) {
        if (len < 7) {
            for (int i = off; i < len + off; i++) for (int j = i; j > off && x[j - 1] > x[j]; j--) swap(x, j, j - 1);
            return;
        }
        int m = off + (len >> 1);
        if (len > 7) {
            int l = off;
            int n = off + len - 1;
            if (len > 40) {
                int s = len / 8;
                l = med3(x, l, l + s, l + 2 * s);
                m = med3(x, m - s, m, m + s);
                n = med3(x, n - 2 * s, n - s, n);
            }
            m = med3(x, l, m, n);
        }
        double v = x[m];
        int a = off;
        int b = a;
        int c = off + len - 1;
        int d = c;
        while (true) {
            while (b <= c && x[b] <= v) {
                if (x[b] == v) swap(x, a++, b);
                b++;
            }
            while (c >= b && x[c] >= v) {
                if (x[c] == v) swap(x, c, d--);
                c--;
            }
            if (b > c) break;
            swap(x, b++, c--);
        }
        int s;
        int n = off + len;
        s = Math.min(a - off, b - a);
        vecswap(x, off, b - s, s);
        s = Math.min(d - c, n - d - 1);
        vecswap(x, b, n - s, s);
        if ((s = b - a) > 1) sort1(x, off, s);
        if ((s = d - c) > 1) sort1(x, n - s, s);
    }
    
    private static void swap(double[] x, int a, int b) {
        double t = x[a];
        x[a] = x[b];
        x[b] = t;
    }
    
    private static void vecswap(double[] x, int a, int b, int n) {
        for (int i = 0; i < n; i++, a++, b++) swap(x, a, b);
    }
    
    private static int med3(double[] x, int a, int b, int c) {
        return (x[a] < x[b] ? (x[b] < x[c] ? b : x[a] < x[c] ? c : a) : (x[b] > x[c] ? b : x[a] > x[c] ? c : a));
    }
    
    private static void sort1(float[] x, int off, int len) {
        if (len < 7) {
            for (int i = off; i < len + off; i++) for (int j = i; j > off && x[j - 1] > x[j]; j--) swap(x, j, j - 1);
            return;
        }
        int m = off + (len >> 1);
        if (len > 7) {
            int l = off;
            int n = off + len - 1;
            if (len > 40) {
                int s = len / 8;
                l = med3(x, l, l + s, l + 2 * s);
                m = med3(x, m - s, m, m + s);
                n = med3(x, n - 2 * s, n - s, n);
            }
            m = med3(x, l, m, n);
        }
        float v = x[m];
        int a = off;
        int b = a;
        int c = off + len - 1;
        int d = c;
        while (true) {
            while (b <= c && x[b] <= v) {
                if (x[b] == v) swap(x, a++, b);
                b++;
            }
            while (c >= b && x[c] >= v) {
                if (x[c] == v) swap(x, c, d--);
                c--;
            }
            if (b > c) break;
            swap(x, b++, c--);
        }
        int s;
        int n = off + len;
        s = Math.min(a - off, b - a);
        vecswap(x, off, b - s, s);
        s = Math.min(d - c, n - d - 1);
        vecswap(x, b, n - s, s);
        if ((s = b - a) > 1) sort1(x, off, s);
        if ((s = d - c) > 1) sort1(x, n - s, s);
    }
    
    private static void swap(float[] x, int a, int b) {
        float t = x[a];
        x[a] = x[b];
        x[b] = t;
    }
    
    private static void vecswap(float[] x, int a, int b, int n) {
        for (int i = 0; i < n; i++, a++, b++) swap(x, a, b);
    }
    
    private static int med3(float[] x, int a, int b, int c) {
        return (x[a] < x[b] ? (x[b] < x[c] ? b : x[a] < x[c] ? c : a) : (x[b] > x[c] ? b : x[a] > x[c] ? c : a));
    }
    
    public static void sort(Object[] a) {
        Object[] aux = (Object[])(Object[])a.clone();
        mergeSort(aux, a, 0, a.length, 0);
    }
    
    public static void sort(Object[] a, int fromIndex, int toIndex) {
        rangeCheck(a.length, fromIndex, toIndex);
        Object[] aux = cloneSubarray(a, fromIndex, toIndex);
        mergeSort(aux, a, fromIndex, toIndex, -fromIndex);
    }
    private static final int INSERTIONSORT_THRESHOLD = 7;
    
    private static Object[] cloneSubarray(Object[] a, int from, int to) {
        int n = to - from;
        Object[] result = (Object[])(Object[])Array.newInstance(a.getClass().getComponentType(), n);
        System.arraycopy(a, from, result, 0, n);
        return result;
    }
    
    private static void mergeSort(Object[] src, Object[] dest, int low, int high, int off) {
        int length = high - low;
        if (length < INSERTIONSORT_THRESHOLD) {
            for (int i = low; i < high; i++) for (int j = i; j > low && ((Comparable)(Comparable)dest[j - 1]).compareTo(dest[j]) > 0; j--) swap(dest, j, j - 1);
            return;
        }
        int destLow = low;
        int destHigh = high;
        low += off;
        high += off;
        int mid = (low + high) >> 1;
        mergeSort(dest, src, low, mid, -off);
        mergeSort(dest, src, mid, high, -off);
        if (((Comparable)(Comparable)src[mid - 1]).compareTo(src[mid]) <= 0) {
            System.arraycopy(src, low, dest, destLow, length);
            return;
        }
        for (int i = destLow, p = low, q = mid; i < destHigh; i++) {
            if (q >= high || p < mid && ((Comparable)(Comparable)src[p]).compareTo(src[q]) <= 0) dest[i] = src[p++]; else dest[i] = src[q++];
        }
    }
    
    private static void swap(Object[] x, int a, int b) {
        Object t = x[a];
        x[a] = x[b];
        x[b] = t;
    }
    
    public static void sort(Object[] a, Comparator c) {
        Object[] aux = (Object[])(Object[])a.clone();
        if (c == null) mergeSort(aux, a, 0, a.length, 0); else mergeSort(aux, a, 0, a.length, 0, c);
    }
    
    public static void sort(Object[] a, int fromIndex, int toIndex, Comparator c) {
        rangeCheck(a.length, fromIndex, toIndex);
        Object[] aux = (Object[])cloneSubarray(a, fromIndex, toIndex);
        if (c == null) mergeSort(aux, a, fromIndex, toIndex, -fromIndex); else mergeSort(aux, a, fromIndex, toIndex, -fromIndex, c);
    }
    
    private static void mergeSort(Object[] src, Object[] dest, int low, int high, int off, Comparator c) {
        int length = high - low;
        if (length < INSERTIONSORT_THRESHOLD) {
            for (int i = low; i < high; i++) for (int j = i; j > low && c.compare(dest[j - 1], dest[j]) > 0; j--) swap(dest, j, j - 1);
            return;
        }
        int destLow = low;
        int destHigh = high;
        low += off;
        high += off;
        int mid = (low + high) >> 1;
        mergeSort(dest, src, low, mid, -off, c);
        mergeSort(dest, src, mid, high, -off, c);
        if (c.compare(src[mid - 1], src[mid]) <= 0) {
            System.arraycopy(src, low, dest, destLow, length);
            return;
        }
        for (int i = destLow, p = low, q = mid; i < destHigh; i++) {
            if (q >= high || p < mid && c.compare(src[p], src[q]) <= 0) dest[i] = src[p++]; else dest[i] = src[q++];
        }
    }
    
    private static void rangeCheck(int arrayLen, int fromIndex, int toIndex) {
        if (fromIndex > toIndex) throw new IllegalArgumentException("fromIndex(" + fromIndex + ") > toIndex(" + toIndex + ")");
        if (fromIndex < 0) throw new ArrayIndexOutOfBoundsException(fromIndex);
        if (toIndex > arrayLen) throw new ArrayIndexOutOfBoundsException(toIndex);
    }
    
    public static int binarySearch(long[] a, long key) {
        int low = 0;
        int high = a.length - 1;
        while (low <= high) {
            int mid = (low + high) >> 1;
            long midVal = a[mid];
            if (midVal < key) low = mid + 1; else if (midVal > key) high = mid - 1; else return mid;
        }
        return -(low + 1);
    }
    
    public static int binarySearch(int[] a, int key) {
        int low = 0;
        int high = a.length - 1;
        while (low <= high) {
            int mid = (low + high) >> 1;
            int midVal = a[mid];
            if (midVal < key) low = mid + 1; else if (midVal > key) high = mid - 1; else return mid;
        }
        return -(low + 1);
    }
    
    public static int binarySearch(short[] a, short key) {
        int low = 0;
        int high = a.length - 1;
        while (low <= high) {
            int mid = (low + high) >> 1;
            short midVal = a[mid];
            if (midVal < key) low = mid + 1; else if (midVal > key) high = mid - 1; else return mid;
        }
        return -(low + 1);
    }
    
    public static int binarySearch(char[] a, char key) {
        int low = 0;
        int high = a.length - 1;
        while (low <= high) {
            int mid = (low + high) >> 1;
            char midVal = a[mid];
            if (midVal < key) low = mid + 1; else if (midVal > key) high = mid - 1; else return mid;
        }
        return -(low + 1);
    }
    
    public static int binarySearch(byte[] a, byte key) {
        int low = 0;
        int high = a.length - 1;
        while (low <= high) {
            int mid = (low + high) >> 1;
            byte midVal = a[mid];
            if (midVal < key) low = mid + 1; else if (midVal > key) high = mid - 1; else return mid;
        }
        return -(low + 1);
    }
    
    public static int binarySearch(double[] a, double key) {
        return binarySearch(a, key, 0, a.length - 1);
    }
    
    private static int binarySearch(double[] a, double key, int low, int high) {
        while (low <= high) {
            int mid = (low + high) >> 1;
            double midVal = a[mid];
            int cmp;
            if (midVal < key) {
                cmp = -1;
            } else if (midVal > key) {
                cmp = 1;
            } else {
                long midBits = Double.doubleToLongBits(midVal);
                long keyBits = Double.doubleToLongBits(key);
                cmp = (midBits == keyBits ? 0 : (midBits < keyBits ? -1 : 1));
            }
            if (cmp < 0) low = mid + 1; else if (cmp > 0) high = mid - 1; else return mid;
        }
        return -(low + 1);
    }
    
    public static int binarySearch(float[] a, float key) {
        return binarySearch(a, key, 0, a.length - 1);
    }
    
    private static int binarySearch(float[] a, float key, int low, int high) {
        while (low <= high) {
            int mid = (low + high) >> 1;
            float midVal = a[mid];
            int cmp;
            if (midVal < key) {
                cmp = -1;
            } else if (midVal > key) {
                cmp = 1;
            } else {
                int midBits = Float.floatToIntBits(midVal);
                int keyBits = Float.floatToIntBits(key);
                cmp = (midBits == keyBits ? 0 : (midBits < keyBits ? -1 : 1));
            }
            if (cmp < 0) low = mid + 1; else if (cmp > 0) high = mid - 1; else return mid;
        }
        return -(low + 1);
    }
    
    public static int binarySearch(Object[] a, Object key) {
        int low = 0;
        int high = a.length - 1;
        while (low <= high) {
            int mid = (low + high) >> 1;
            Comparable midVal = (Comparable)(Comparable)a[mid];
            int cmp = midVal.compareTo(key);
            if (cmp < 0) low = mid + 1; else if (cmp > 0) high = mid - 1; else return mid;
        }
        return -(low + 1);
    }
    
    public static int binarySearch(Object[] a, Object key, Comparator c) {
        if (c == null) {
            return binarySearch(a, key);
        }
        int low = 0;
        int high = a.length - 1;
        while (low <= high) {
            int mid = (low + high) >> 1;
            Object midVal = a[mid];
            int cmp = c.compare(midVal, key);
            if (cmp < 0) low = mid + 1; else if (cmp > 0) high = mid - 1; else return mid;
        }
        return -(low + 1);
    }
    
    public static boolean equals(long[] a, long[] a2) {
        if (a == a2) return true;
        if (a == null || a2 == null) return false;
        int length = a.length;
        if (a2.length != length) return false;
        for (int i = 0; i < length; i++) if (a[i] != a2[i]) return false;
        return true;
    }
    
    public static boolean equals(int[] a, int[] a2) {
        if (a == a2) return true;
        if (a == null || a2 == null) return false;
        int length = a.length;
        if (a2.length != length) return false;
        for (int i = 0; i < length; i++) if (a[i] != a2[i]) return false;
        return true;
    }
    
    public static boolean equals(short[] a, short[] a2) {
        if (a == a2) return true;
        if (a == null || a2 == null) return false;
        int length = a.length;
        if (a2.length != length) return false;
        for (int i = 0; i < length; i++) if (a[i] != a2[i]) return false;
        return true;
    }
    
    public static boolean equals(char[] a, char[] a2) {
        if (a == a2) return true;
        if (a == null || a2 == null) return false;
        int length = a.length;
        if (a2.length != length) return false;
        for (int i = 0; i < length; i++) if (a[i] != a2[i]) return false;
        return true;
    }
    
    public static boolean equals(byte[] a, byte[] a2) {
        if (a == a2) return true;
        if (a == null || a2 == null) return false;
        int length = a.length;
        if (a2.length != length) return false;
        for (int i = 0; i < length; i++) if (a[i] != a2[i]) return false;
        return true;
    }
    
    public static boolean equals(boolean[] a, boolean[] a2) {
        if (a == a2) return true;
        if (a == null || a2 == null) return false;
        int length = a.length;
        if (a2.length != length) return false;
        for (int i = 0; i < length; i++) if (a[i] != a2[i]) return false;
        return true;
    }
    
    public static boolean equals(double[] a, double[] a2) {
        if (a == a2) return true;
        if (a == null || a2 == null) return false;
        int length = a.length;
        if (a2.length != length) return false;
        for (int i = 0; i < length; i++) if (Double.doubleToLongBits(a[i]) != Double.doubleToLongBits(a2[i])) return false;
        return true;
    }
    
    public static boolean equals(float[] a, float[] a2) {
        if (a == a2) return true;
        if (a == null || a2 == null) return false;
        int length = a.length;
        if (a2.length != length) return false;
        for (int i = 0; i < length; i++) if (Float.floatToIntBits(a[i]) != Float.floatToIntBits(a2[i])) return false;
        return true;
    }
    
    public static boolean equals(Object[] a, Object[] a2) {
        if (a == a2) return true;
        if (a == null || a2 == null) return false;
        int length = a.length;
        if (a2.length != length) return false;
        for (int i = 0; i < length; i++) {
            Object o1 = a[i];
            Object o2 = a2[i];
            if (!(o1 == null ? o2 == null : o1.equals(o2))) return false;
        }
        return true;
    }
    
    public static void fill(long[] a, long val) {
        fill(a, 0, a.length, val);
    }
    
    public static void fill(long[] a, int fromIndex, int toIndex, long val) {
        rangeCheck(a.length, fromIndex, toIndex);
        for (int i = fromIndex; i < toIndex; i++) a[i] = val;
    }
    
    public static void fill(int[] a, int val) {
        fill(a, 0, a.length, val);
    }
    
    public static void fill(int[] a, int fromIndex, int toIndex, int val) {
        rangeCheck(a.length, fromIndex, toIndex);
        for (int i = fromIndex; i < toIndex; i++) a[i] = val;
    }
    
    public static void fill(short[] a, short val) {
        fill(a, 0, a.length, val);
    }
    
    public static void fill(short[] a, int fromIndex, int toIndex, short val) {
        rangeCheck(a.length, fromIndex, toIndex);
        for (int i = fromIndex; i < toIndex; i++) a[i] = val;
    }
    
    public static void fill(char[] a, char val) {
        fill(a, 0, a.length, val);
    }
    
    public static void fill(char[] a, int fromIndex, int toIndex, char val) {
        rangeCheck(a.length, fromIndex, toIndex);
        for (int i = fromIndex; i < toIndex; i++) a[i] = val;
    }
    
    public static void fill(byte[] a, byte val) {
        fill(a, 0, a.length, val);
    }
    
    public static void fill(byte[] a, int fromIndex, int toIndex, byte val) {
        rangeCheck(a.length, fromIndex, toIndex);
        for (int i = fromIndex; i < toIndex; i++) a[i] = val;
    }
    
    public static void fill(boolean[] a, boolean val) {
        fill(a, 0, a.length, val);
    }
    
    public static void fill(boolean[] a, int fromIndex, int toIndex, boolean val) {
        rangeCheck(a.length, fromIndex, toIndex);
        for (int i = fromIndex; i < toIndex; i++) a[i] = val;
    }
    
    public static void fill(double[] a, double val) {
        fill(a, 0, a.length, val);
    }
    
    public static void fill(double[] a, int fromIndex, int toIndex, double val) {
        rangeCheck(a.length, fromIndex, toIndex);
        for (int i = fromIndex; i < toIndex; i++) a[i] = val;
    }
    
    public static void fill(float[] a, float val) {
        fill(a, 0, a.length, val);
    }
    
    public static void fill(float[] a, int fromIndex, int toIndex, float val) {
        rangeCheck(a.length, fromIndex, toIndex);
        for (int i = fromIndex; i < toIndex; i++) a[i] = val;
    }
    
    public static void fill(Object[] a, Object val) {
        Arrays.fill(a, 0, a.length, val);
    }
    
    public static void fill(Object[] a, int fromIndex, int toIndex, Object val) {
        rangeCheck(a.length, fromIndex, toIndex);
        for (int i = fromIndex; i < toIndex; i++) a[i] = val;
    }
    
    public static List asList(Object[] a) {
        return new Arrays$ArrayList(a);
    }
    {
    }
    
    public static int hashCode(long[] a) {
        if (a == null) return 0;
        int result = 1;
        for (long[] arr$ = a, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
            long element = arr$[i$];
            {
                int elementHash = (int)(element ^ (element >>> 32));
                result = 31 * result + elementHash;
            }
        }
        return result;
    }
    
    public static int hashCode(int[] a) {
        if (a == null) return 0;
        int result = 1;
        for (int[] arr$ = a, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
            int element = arr$[i$];
            result = 31 * result + element;
        }
        return result;
    }
    
    public static int hashCode(short[] a) {
        if (a == null) return 0;
        int result = 1;
        for (short[] arr$ = a, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
            short element = arr$[i$];
            result = 31 * result + element;
        }
        return result;
    }
    
    public static int hashCode(char[] a) {
        if (a == null) return 0;
        int result = 1;
        for (char[] arr$ = a, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
            char element = arr$[i$];
            result = 31 * result + element;
        }
        return result;
    }
    
    public static int hashCode(byte[] a) {
        if (a == null) return 0;
        int result = 1;
        for (byte[] arr$ = a, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
            byte element = arr$[i$];
            result = 31 * result + element;
        }
        return result;
    }
    
    public static int hashCode(boolean[] a) {
        if (a == null) return 0;
        int result = 1;
        for (boolean[] arr$ = a, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
            boolean element = arr$[i$];
            result = 31 * result + (element ? 1231 : 1237);
        }
        return result;
    }
    
    public static int hashCode(float[] a) {
        if (a == null) return 0;
        int result = 1;
        for (float[] arr$ = a, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
            float element = arr$[i$];
            result = 31 * result + Float.floatToIntBits(element);
        }
        return result;
    }
    
    public static int hashCode(double[] a) {
        if (a == null) return 0;
        int result = 1;
        for (double[] arr$ = a, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
            double element = arr$[i$];
            {
                long bits = Double.doubleToLongBits(element);
                result = 31 * result + (int)(bits ^ (bits >>> 32));
            }
        }
        return result;
    }
    
    public static int hashCode(Object[] a) {
        if (a == null) return 0;
        int result = 1;
        for (Object[] arr$ = a, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
            Object element = arr$[i$];
            result = 31 * result + (element == null ? 0 : element.hashCode());
        }
        return result;
    }
    
    public static int deepHashCode(Object[] a) {
        if (a == null) return 0;
        int result = 1;
        for (Object[] arr$ = a, len$ = arr$.length, i$ = 0; i$ < len$; ++i$) {
            Object element = arr$[i$];
            {
                int elementHash = 0;
                if (element instanceof Object[]) elementHash = deepHashCode((Object[])(Object[])element); else if (element instanceof byte[]) elementHash = hashCode((byte[])(byte[])element); else if (element instanceof short[]) elementHash = hashCode((short[])(short[])element); else if (element instanceof int[]) elementHash = hashCode((int[])(int[])element); else if (element instanceof long[]) elementHash = hashCode((long[])(long[])element); else if (element instanceof char[]) elementHash = hashCode((char[])(char[])element); else if (element instanceof float[]) elementHash = hashCode((float[])(float[])element); else if (element instanceof double[]) elementHash = hashCode((double[])(double[])element); else if (element instanceof boolean[]) elementHash = hashCode((boolean[])(boolean[])element); else if (element != null) elementHash = element.hashCode();
                result = 31 * result + elementHash;
            }
        }
        return result;
    }
    
    public static boolean deepEquals(Object[] a1, Object[] a2) {
        if (a1 == a2) return true;
        if (a1 == null || a2 == null) return false;
        int length = a1.length;
        if (a2.length != length) return false;
        for (int i = 0; i < length; i++) {
            Object e1 = a1[i];
            Object e2 = a2[i];
            if (e1 == e2) continue;
            if (e1 == null) return false;
            boolean eq;
            if (e1 instanceof Object[] && e2 instanceof Object[]) eq = deepEquals((Object[])(Object[])e1, (Object[])(Object[])e2); else if (e1 instanceof byte[] && e2 instanceof byte[]) eq = equals((byte[])(byte[])e1, (byte[])(byte[])e2); else if (e1 instanceof short[] && e2 instanceof short[]) eq = equals((short[])(short[])e1, (short[])(short[])e2); else if (e1 instanceof int[] && e2 instanceof int[]) eq = equals((int[])(int[])e1, (int[])(int[])e2); else if (e1 instanceof long[] && e2 instanceof long[]) eq = equals((long[])(long[])e1, (long[])(long[])e2); else if (e1 instanceof char[] && e2 instanceof char[]) eq = equals((char[])(char[])e1, (char[])(char[])e2); else if (e1 instanceof float[] && e2 instanceof float[]) eq = equals((float[])(float[])e1, (float[])(float[])e2); else if (e1 instanceof double[] && e2 instanceof double[]) eq = equals((double[])(double[])e1, (double[])(double[])e2); else if (e1 instanceof boolean[] && e2 instanceof boolean[]) eq = equals((boolean[])(boolean[])e1, (boolean[])(boolean[])e2); else eq = e1.equals(e2);
            if (!eq) return false;
        }
        return true;
    }
    
    public static String toString(long[] a) {
        if (a == null) return "null";
        if (a.length == 0) return "[]";
        StringBuilder buf = new StringBuilder();
        buf.append('[');
        buf.append(a[0]);
        for (int i = 1; i < a.length; i++) {
            buf.append(", ");
            buf.append(a[i]);
        }
        buf.append("]");
        return buf.toString();
    }
    
    public static String toString(int[] a) {
        if (a == null) return "null";
        if (a.length == 0) return "[]";
        StringBuilder buf = new StringBuilder();
        buf.append('[');
        buf.append(a[0]);
        for (int i = 1; i < a.length; i++) {
            buf.append(", ");
            buf.append(a[i]);
        }
        buf.append("]");
        return buf.toString();
    }
    
    public static String toString(short[] a) {
        if (a == null) return "null";
        if (a.length == 0) return "[]";
        StringBuilder buf = new StringBuilder();
        buf.append('[');
        buf.append(a[0]);
        for (int i = 1; i < a.length; i++) {
            buf.append(", ");
            buf.append(a[i]);
        }
        buf.append("]");
        return buf.toString();
    }
    
    public static String toString(char[] a) {
        if (a == null) return "null";
        if (a.length == 0) return "[]";
        StringBuilder buf = new StringBuilder();
        buf.append('[');
        buf.append(a[0]);
        for (int i = 1; i < a.length; i++) {
            buf.append(", ");
            buf.append(a[i]);
        }
        buf.append("]");
        return buf.toString();
    }
    
    public static String toString(byte[] a) {
        if (a == null) return "null";
        if (a.length == 0) return "[]";
        StringBuilder buf = new StringBuilder();
        buf.append('[');
        buf.append(a[0]);
        for (int i = 1; i < a.length; i++) {
            buf.append(", ");
            buf.append(a[i]);
        }
        buf.append("]");
        return buf.toString();
    }
    
    public static String toString(boolean[] a) {
        if (a == null) return "null";
        if (a.length == 0) return "[]";
        StringBuilder buf = new StringBuilder();
        buf.append('[');
        buf.append(a[0]);
        for (int i = 1; i < a.length; i++) {
            buf.append(", ");
            buf.append(a[i]);
        }
        buf.append("]");
        return buf.toString();
    }
    
    public static String toString(float[] a) {
        if (a == null) return "null";
        if (a.length == 0) return "[]";
        StringBuilder buf = new StringBuilder();
        buf.append('[');
        buf.append(a[0]);
        for (int i = 1; i < a.length; i++) {
            buf.append(", ");
            buf.append(a[i]);
        }
        buf.append("]");
        return buf.toString();
    }
    
    public static String toString(double[] a) {
        if (a == null) return "null";
        if (a.length == 0) return "[]";
        StringBuilder buf = new StringBuilder();
        buf.append('[');
        buf.append(a[0]);
        for (int i = 1; i < a.length; i++) {
            buf.append(", ");
            buf.append(a[i]);
        }
        buf.append("]");
        return buf.toString();
    }
    
    public static String toString(Object[] a) {
        if (a == null) return "null";
        if (a.length == 0) return "[]";
        StringBuilder buf = new StringBuilder();
        for (int i = 0; i < a.length; i++) {
            if (i == 0) buf.append('['); else buf.append(", ");
            buf.append(String.valueOf(a[i]));
        }
        buf.append("]");
        return buf.toString();
    }
    
    public static String deepToString(Object[] a) {
        if (a == null) return "null";
        int bufLen = 20 * a.length;
        if (a.length != 0 && bufLen <= 0) bufLen = Integer.MAX_VALUE;
        StringBuilder buf = new StringBuilder(bufLen);
        deepToString(a, buf, new HashSet());
        return buf.toString();
    }
    
    private static void deepToString(Object[] a, StringBuilder buf, Set dejaVu) {
        if (a == null) {
            buf.append("null");
            return;
        }
        dejaVu.add(a);
        buf.append('[');
        for (int i = 0; i < a.length; i++) {
            if (i != 0) buf.append(", ");
            Object element = a[i];
            if (element == null) {
                buf.append("null");
            } else {
                Class eClass = element.getClass();
                if (eClass.isArray()) {
                    if (eClass == byte[].class) buf.append(toString((byte[])(byte[])element)); else if (eClass == short[].class) buf.append(toString((short[])(short[])element)); else if (eClass == int[].class) buf.append(toString((int[])(int[])element)); else if (eClass == long[].class) buf.append(toString((long[])(long[])element)); else if (eClass == char[].class) buf.append(toString((char[])(char[])element)); else if (eClass == float[].class) buf.append(toString((float[])(float[])element)); else if (eClass == double[].class) buf.append(toString((double[])(double[])element)); else if (eClass == boolean[].class) buf.append(toString((boolean[])(boolean[])element)); else {
                        if (dejaVu.contains(element)) buf.append("[...]"); else deepToString((Object[])(Object[])element, buf, dejaVu);
                    }
                } else {
                    buf.append(element.toString());
                }
            }
        }
        buf.append("]");
        dejaVu.remove(a);
    }
}
