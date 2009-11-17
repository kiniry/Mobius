package java.lang;

import java.io.*;

class UNIXProcess$Gate {
    
    /*synthetic*/ UNIXProcess$Gate(java.lang.UNIXProcess$1 x0) {
        this();
    }
    
    private UNIXProcess$Gate() {
        
    }
    private boolean exited = false;
    private IOException savedException;
    
    synchronized void exit() {
        exited = true;
        this.notify();
    }
    
    synchronized void waitForExit() {
        boolean interrupted = false;
        while (!exited) {
            try {
                this.wait();
            } catch (InterruptedException e) {
                interrupted = true;
            }
        }
        if (interrupted) {
            Thread.currentThread().interrupt();
        }
    }
    
    void setException(IOException e) {
        savedException = e;
    }
    
    IOException getException() {
        return savedException;
    }
}
