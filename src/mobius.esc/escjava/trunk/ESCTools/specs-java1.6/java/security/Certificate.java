package java.security;

import java.io.*;


public interface Certificate {
    
    public abstract Principal getGuarantor();
    
    public abstract Principal getPrincipal();
    
    public abstract PublicKey getPublicKey();
    
    public abstract void encode(OutputStream stream) throws KeyException, IOException;
    
    public abstract void decode(InputStream stream) throws KeyException, IOException;
    
    public abstract String getFormat();
    
    public String toString(boolean detailed);
}
