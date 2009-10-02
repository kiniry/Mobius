package java.rmi.server;

public abstract class RemoteStub extends RemoteObject {
    private static final long serialVersionUID = -1585587260594494182L;
    
    protected RemoteStub() {
        
    }
    
    protected RemoteStub(RemoteRef ref) {
        super(ref);
    }
    
    
    protected static void setRef(RemoteStub stub, RemoteRef ref) {
        throw new UnsupportedOperationException();
    }
}
