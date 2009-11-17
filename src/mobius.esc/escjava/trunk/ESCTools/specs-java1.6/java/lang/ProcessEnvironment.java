package java.lang;

import java.io.*;
import java.util.*;

final class ProcessEnvironment {
    
    /*synthetic*/ static void access$400(String x0) {
        validateValue(x0);
    }
    
    /*synthetic*/ static int access$300(byte[] x0, byte[] x1) {
        return arrayCompare(x0, x1);
    }
    
    /*synthetic*/ static void access$200(String x0) {
        validateVariable(x0);
    }
    
    /*synthetic*/ static int access$100(byte[] x0) {
        return arrayHash(x0);
    }
    
    /*synthetic*/ static boolean access$000(byte[] x0, byte[] x1) {
        return arrayEquals(x0, x1);
    }
    private static final HashMap theEnvironment;
    private static final Map theUnmodifiableEnvironment;
    static final int MIN_NAME_LENGTH = 0;
    static {
        byte[][] environ = environ();
        theEnvironment = new HashMap(environ.length / 2 + 3);
        for (int i = environ.length - 1; i > 0; i -= 2) theEnvironment.put(ProcessEnvironment$Variable.valueOf(environ[i - 1]), ProcessEnvironment$Value.valueOf(environ[i]));
        theUnmodifiableEnvironment = Collections.unmodifiableMap(new ProcessEnvironment$StringEnvironment(theEnvironment));
    }
    
    static String getenv(String name) {
        return (String)theUnmodifiableEnvironment.get(name);
    }
    
    static Map getenv() {
        return theUnmodifiableEnvironment;
    }
    
    static Map environment() {
        return new ProcessEnvironment$StringEnvironment((Map)((Map)theEnvironment.clone()));
    }
    
    static Map emptyEnvironment(int capacity) {
        return new ProcessEnvironment$StringEnvironment(new HashMap(capacity));
    }
    
    private static native byte[][] environ();
    
    private ProcessEnvironment() {
        
    }
    
    private static void validateVariable(String name) {
        if (name.indexOf('=') != -1 || name.indexOf('\000') != -1) throw new IllegalArgumentException("Invalid environment variable name: \"" + name + "\"");
    }
    
    private static void validateValue(String value) {
        if (value.indexOf('\000') != -1) throw new IllegalArgumentException("Invalid environment variable value: \"" + value + "\"");
    }
    {
    }
    {
    }
    {
    }
    {
    }
    
    static byte[] toEnvironmentBlock(Map map, int[] envc) {
        return map == null ? null : ((ProcessEnvironment$StringEnvironment)(ProcessEnvironment$StringEnvironment)map).toEnvironmentBlock(envc);
    }
    {
    }
    {
    }
    {
    }
    {
    }
    
    private static int arrayCompare(byte[] x, byte[] y) {
        int min = x.length < y.length ? x.length : y.length;
        for (int i = 0; i < min; i++) if (x[i] != y[i]) return x[i] - y[i];
        return x.length - y.length;
    }
    
    private static boolean arrayEquals(byte[] x, byte[] y) {
        if (x.length != y.length) return false;
        for (int i = 0; i < x.length; i++) if (x[i] != y[i]) return false;
        return true;
    }
    
    private static int arrayHash(byte[] x) {
        int hash = 0;
        for (int i = 0; i < x.length; i++) hash = 31 * hash + x[i];
        return hash;
    }
}
