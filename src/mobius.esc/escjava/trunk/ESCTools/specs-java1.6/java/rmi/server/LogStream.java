package java.rmi.server;

import java.io.*;
import java.util.*;


public class LogStream extends PrintStream {
    private static Hashtable known = new Hashtable(5);
    private static PrintStream defaultStream = System.err;
    private String name;
    private OutputStream logOut;
    private OutputStreamWriter logWriter;
    private StringBuffer buffer = new StringBuffer();
    private ByteArrayOutputStream bufOut;
    
    
    private LogStream(String name, OutputStream out) {
        super(new ByteArrayOutputStream());
        bufOut = (ByteArrayOutputStream)(ByteArrayOutputStream)super.out;
        this.name = name;
        setOutputStream(out);
    }
    
    
    public static LogStream log(String name) {
        LogStream stream;
        synchronized (known) {
            stream = (LogStream)(LogStream)known.get(name);
            if (stream == null) {
                stream = new LogStream(name, defaultStream);
            }
            known.put(name, stream);
        }
        return stream;
    }
    
    
    public static synchronized PrintStream getDefaultStream() {
        return defaultStream;
    }
    
    
    public static synchronized void setDefaultStream(PrintStream newDefault) {
        defaultStream = newDefault;
    }
    
    
    public synchronized OutputStream getOutputStream() {
        return logOut;
    }
    
    
    public synchronized void setOutputStream(OutputStream out) {
        logOut = out;
        logWriter = new OutputStreamWriter(logOut);
    }
    
    
    public void write(int b) {
        if (b == '\n') {
            synchronized (this) {
                synchronized (logOut) {
                    buffer.setLength(0);
                    ;
                    buffer.append((new Date()).toString());
                    buffer.append(':');
                    buffer.append(name);
                    buffer.append(':');
                    buffer.append(Thread.currentThread().getName());
                    buffer.append(':');
                    try {
                        logWriter.write(buffer.toString());
                        logWriter.flush();
                        bufOut.writeTo(logOut);
                        logOut.write(b);
                        logOut.flush();
                    } catch (IOException e) {
                        setError();
                    } finally {
                        bufOut.reset();
                    }
                }
            }
        } else super.write(b);
    }
    
    
    public void write(byte[] b, int off, int len) {
        if (len < 0) throw new ArrayIndexOutOfBoundsException(len);
        for (int i = 0; i < len; ++i) write(b[off + i]);
    }
    
    
    public String toString() {
        return name;
    }
    public static final int SILENT = 0;
    public static final int BRIEF = 10;
    public static final int VERBOSE = 20;
    
    
    public static int parseLevel(String s) {
        if ((s == null) || (s.length() < 1)) return -1;
        try {
            return Integer.parseInt(s);
        } catch (NumberFormatException e) {
        }
        if (s.length() < 1) return -1;
        if ("SILENT".startsWith(s.toUpperCase())) return SILENT; else if ("BRIEF".startsWith(s.toUpperCase())) return BRIEF; else if ("VERBOSE".startsWith(s.toUpperCase())) return VERBOSE;
        return -1;
    }
}
