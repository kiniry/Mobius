package java.nio.channels;

import java.io.*;

public class FileChannel$MapMode {
    public static final FileChannel$MapMode READ_ONLY = new FileChannel$MapMode("READ_ONLY");
    public static final FileChannel$MapMode READ_WRITE = new FileChannel$MapMode("READ_WRITE");
    public static final FileChannel$MapMode PRIVATE = new FileChannel$MapMode("PRIVATE");
    private final String name;
    
    private FileChannel$MapMode(String name) {
        
        this.name = name;
    }
    
    public String toString() {
        return name;
    }
}
