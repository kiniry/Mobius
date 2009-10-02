package java.lang;

import java.io.*;

final class UNIXProcess extends Process {
    
    /*synthetic*/ static int access$1102(UNIXProcess x0, int x1) {
        return x0.exitcode = x1;
    }
    
    /*synthetic*/ static boolean access$1002(UNIXProcess x0, boolean x1) {
        return x0.hasExited = x1;
    }
    
    /*synthetic*/ static int access$900(UNIXProcess x0, int x1) {
        return x0.waitForProcessExit(x1);
    }
    
    /*synthetic*/ static InputStream access$802(UNIXProcess x0, InputStream x1) {
        return x0.stderr_stream = x1;
    }
    
    /*synthetic*/ static InputStream access$702(UNIXProcess x0, InputStream x1) {
        return x0.stdout_stream = x1;
    }
    
    /*synthetic*/ static OutputStream access$602(UNIXProcess x0, OutputStream x1) {
        return x0.stdin_stream = x1;
    }
    
    /*synthetic*/ static int access$500(UNIXProcess x0, byte[] x1, byte[] x2, int x3, byte[] x4, int x5, byte[] x6, boolean x7, FileDescriptor x8, FileDescriptor x9, FileDescriptor x10) throws IOException {
        return x0.forkAndExec(x1, x2, x3, x4, x5, x6, x7, x8, x9, x10);
    }
    
    /*synthetic*/ static FileDescriptor access$400(UNIXProcess x0) {
        return x0.stderr_fd;
    }
    
    /*synthetic*/ static FileDescriptor access$300(UNIXProcess x0) {
        return x0.stdout_fd;
    }
    
    /*synthetic*/ static FileDescriptor access$200(UNIXProcess x0) {
        return x0.stdin_fd;
    }
    
    /*synthetic*/ static int access$102(UNIXProcess x0, int x1) {
        return x0.pid = x1;
    }
    
    /*synthetic*/ static int access$100(UNIXProcess x0) {
        return x0.pid;
    }
    private FileDescriptor stdin_fd;
    private FileDescriptor stdout_fd;
    private FileDescriptor stderr_fd;
    private int pid;
    private int exitcode;
    private boolean hasExited;
    private OutputStream stdin_stream;
    private InputStream stdout_stream;
    private InputStream stderr_stream;
    
    private native int waitForProcessExit(int pid);
    
    private native int forkAndExec(byte[] prog, byte[] argBlock, int argc, byte[] envBlock, int envc, byte[] dir, boolean redirectErrorStream, FileDescriptor stdin_fd, FileDescriptor stdout_fd, FileDescriptor stderr_fd) throws IOException;
    {
    }
    
    UNIXProcess(final byte[] prog, final byte[] argBlock, final int argc, final byte[] envBlock, final int envc, final byte[] dir, final boolean redirectErrorStream) throws IOException {
        
        stdin_fd = new FileDescriptor();
        stdout_fd = new FileDescriptor();
        stderr_fd = new FileDescriptor();
        final UNIXProcess$Gate gate = new UNIXProcess$Gate(null);
        java.security.AccessController.doPrivileged(new UNIXProcess$1(this, prog, argBlock, argc, envBlock, envc, dir, redirectErrorStream, gate));
        gate.waitForExit();
        IOException e = gate.getException();
        if (e != null) throw new IOException(e.toString());
    }
    
    public OutputStream getOutputStream() {
        return stdin_stream;
    }
    
    public InputStream getInputStream() {
        return stdout_stream;
    }
    
    public InputStream getErrorStream() {
        return stderr_stream;
    }
    
    public synchronized int waitFor() throws InterruptedException {
        while (!hasExited) {
            wait();
        }
        return exitcode;
    }
    
    public synchronized int exitValue() {
        if (!hasExited) {
            throw new IllegalThreadStateException("process hasn\'t exited");
        }
        return exitcode;
    }
    
    private static native void destroyProcess(int pid);
    
    public void destroy() {
        synchronized (this) {
            if (!hasExited) destroyProcess(pid);
        }
        try {
            stdin_stream.close();
            stdout_stream.close();
            stderr_stream.close();
        } catch (IOException e) {
        }
    }
}
