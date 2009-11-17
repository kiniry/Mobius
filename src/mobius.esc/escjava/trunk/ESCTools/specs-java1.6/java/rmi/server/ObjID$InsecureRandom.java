package java.rmi.server;

import java.util.Random;

final class ObjID$InsecureRandom extends Random {
    
    /*synthetic*/ ObjID$InsecureRandom(java.rmi.server.ObjID$1 x0) {
        this();
    }
    
    private ObjID$InsecureRandom() {
        
    }
    private static final long serialVersionUID = -698228687531590145L;
    private long nextNum;
    
    public synchronized long nextLong() {
        return nextNum++;
    }
}
