package java.util;

import java.io.*;
import java.util.concurrent.atomic.AtomicLong;

public class Random implements java.io.Serializable {
    static final long serialVersionUID = 3905348978240129619L;
    private AtomicLong seed;
    private static final long multiplier = 25214903917L;
    private static final long addend = 11L;
    private static final long mask = (1L << 48) - 1;
    
    public Random() {
        this(++seedUniquifier + System.nanoTime());
    }
    private static volatile long seedUniquifier = 8682522807148012L;
    
    public Random(long seed) {
        
        this.seed = new AtomicLong(0L);
        setSeed(seed);
    }
    
    public synchronized void setSeed(long seed) {
        seed = (seed ^ multiplier) & mask;
        this.seed.set(seed);
        haveNextNextGaussian = false;
    }
    
    protected int next(int bits) {
        long oldseed;
        long nextseed;
        AtomicLong seed = this.seed;
        do {
            oldseed = seed.get();
            nextseed = (oldseed * multiplier + addend) & mask;
        }         while (!seed.compareAndSet(oldseed, nextseed));
        return (int)(nextseed >>> (48 - bits));
    }
    private static final int BITS_PER_BYTE = 8;
    private static final int BYTES_PER_INT = 4;
    
    public void nextBytes(byte[] bytes) {
        int numRequested = bytes.length;
        int numGot = 0;
        int rnd = 0;
        while (true) {
            for (int i = 0; i < BYTES_PER_INT; i++) {
                if (numGot == numRequested) return;
                rnd = (i == 0 ? next(BITS_PER_BYTE * BYTES_PER_INT) : rnd >> BITS_PER_BYTE);
                bytes[numGot++] = (byte)rnd;
            }
        }
    }
    
    public int nextInt() {
        return next(32);
    }
    
    public int nextInt(int n) {
        if (n <= 0) throw new IllegalArgumentException("n must be positive");
        if ((n & -n) == n) return (int)((n * (long)next(31)) >> 31);
        int bits;
        int val;
        do {
            bits = next(31);
            val = bits % n;
        }         while (bits - val + (n - 1) < 0);
        return val;
    }
    
    public long nextLong() {
        return ((long)(next(32)) << 32) + next(32);
    }
    
    public boolean nextBoolean() {
        return next(1) != 0;
    }
    
    public float nextFloat() {
        int i = next(24);
        return i / ((float)(1 << 24));
    }
    
    public double nextDouble() {
        long l = ((long)(next(26)) << 27) + next(27);
        return l / (double)(1L << 53);
    }
    private double nextNextGaussian;
    private boolean haveNextNextGaussian = false;
    
    public synchronized double nextGaussian() {
        if (haveNextNextGaussian) {
            haveNextNextGaussian = false;
            return nextNextGaussian;
        } else {
            double v1;
            double v2;
            double s;
            do {
                v1 = 2 * nextDouble() - 1;
                v2 = 2 * nextDouble() - 1;
                s = v1 * v1 + v2 * v2;
            }             while (s >= 1 || s == 0);
            double multiplier = Math.sqrt(-2 * Math.log(s) / s);
            nextNextGaussian = v2 * multiplier;
            haveNextNextGaussian = true;
            return v1 * multiplier;
        }
    }
    private static final ObjectStreamField[] serialPersistentFields = {new ObjectStreamField("seed", Long.TYPE), new ObjectStreamField("nextNextGaussian", Double.TYPE), new ObjectStreamField("haveNextNextGaussian", Boolean.TYPE)};
    
    private void readObject(java.io.ObjectInputStream s) throws java.io.IOException, ClassNotFoundException {
        ObjectInputStream$GetField fields = s.readFields();
        long seedVal;
        seedVal = (long)fields.get("seed", -1L);
        if (seedVal < 0) throw new java.io.StreamCorruptedException("Random: invalid seed");
        seed = new AtomicLong(seedVal);
        nextNextGaussian = fields.get("nextNextGaussian", 0.0);
        haveNextNextGaussian = fields.get("haveNextNextGaussian", false);
    }
    
    private synchronized void writeObject(ObjectOutputStream s) throws IOException {
        ObjectOutputStream$PutField fields = s.putFields();
        fields.put("seed", seed.get());
        fields.put("nextNextGaussian", nextNextGaussian);
        fields.put("haveNextNextGaussian", haveNextNextGaussian);
        s.writeFields();
    }
}
