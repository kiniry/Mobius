package java.rmi.activation;

import java.rmi.MarshalledObject;

public final class ActivationDesc implements java.io.Serializable {
    private ActivationGroupID groupID;
    private String className;
    private String location;
    private MarshalledObject data;
    private boolean restart;
    private static final long serialVersionUID = 7455834104417690957L;
    
    public ActivationDesc(String className, String location, MarshalledObject data) throws ActivationException {
        this(ActivationGroup.internalCurrentGroupID(), className, location, data, false);
    }
    
    public ActivationDesc(String className, String location, MarshalledObject data, boolean restart) throws ActivationException {
        this(ActivationGroup.internalCurrentGroupID(), className, location, data, restart);
    }
    
    public ActivationDesc(ActivationGroupID groupID, String className, String location, MarshalledObject data) {
        this(groupID, className, location, data, false);
    }
    
    public ActivationDesc(ActivationGroupID groupID, String className, String location, MarshalledObject data, boolean restart) {
        
        if (groupID == null) throw new IllegalArgumentException("groupID can\'t be null");
        this.groupID = groupID;
        this.className = className;
        this.location = location;
        this.data = data;
        this.restart = restart;
    }
    
    public ActivationGroupID getGroupID() {
        return groupID;
    }
    
    public String getClassName() {
        return className;
    }
    
    public String getLocation() {
        return location;
    }
    
    public MarshalledObject getData() {
        return data;
    }
    
    public boolean getRestartMode() {
        return restart;
    }
    
    public boolean equals(Object obj) {
        if (obj instanceof ActivationDesc) {
            ActivationDesc desc = (ActivationDesc)(ActivationDesc)obj;
            return ((groupID == null ? desc.groupID == null : groupID.equals(desc.groupID)) && (className == null ? desc.className == null : className.equals(desc.className)) && (location == null ? desc.location == null : location.equals(desc.location)) && (data == null ? desc.data == null : data.equals(desc.data)) && (restart == desc.restart));
        } else {
            return false;
        }
    }
    
    public int hashCode() {
        return ((location == null ? 0 : location.hashCode() << 24) ^ (groupID == null ? 0 : groupID.hashCode() << 16) ^ (className == null ? 0 : className.hashCode() << 9) ^ (data == null ? 0 : data.hashCode() << 1) ^ (restart ? 1 : 0));
    }
}
