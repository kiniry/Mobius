package java.rmi.dgc;

public final class Lease implements java.io.Serializable {
    private VMID vmid;
    private long value;
    private static final long serialVersionUID = -5713411624328831948L;
    
    public Lease(VMID id, long duration) {
        
        vmid = id;
        value = duration;
    }
    
    public VMID getVMID() {
        return vmid;
    }
    
    public long getValue() {
        return value;
    }
}
