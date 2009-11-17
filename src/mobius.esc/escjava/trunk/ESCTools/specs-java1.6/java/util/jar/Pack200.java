package java.util.jar;

public abstract class Pack200 {
    
    private Pack200() {
        
    }
    
    public static synchronized Pack200$Packer newPacker() {
        return (Pack200$Packer)(Pack200$Packer)newInstance(PACK_PROVIDER);
    }
    
    public static Pack200$Unpacker newUnpacker() {
        return (Pack200$Unpacker)(Pack200$Unpacker)newInstance(UNPACK_PROVIDER);
    }
    {
    }
    {
    }
    private static final String PACK_PROVIDER = "java.util.jar.Pack200.Packer";
    private static final String UNPACK_PROVIDER = "java.util.jar.Pack200.Unpacker";
    private static Class packerImpl;
    private static Class unpackerImpl;
    
    private static synchronized Object newInstance(String prop) {
        String implName = "(unknown)";
        try {
            Class impl = (prop == PACK_PROVIDER) ? packerImpl : unpackerImpl;
            if (impl == null) {
                implName = (String)(String)java.security.AccessController.doPrivileged(new sun.security.action.GetPropertyAction(prop, ""));
                if (implName != null && !implName.equals("")) impl = Class.forName(implName); else if (prop == PACK_PROVIDER) impl = com.sun.java.util.jar.pack.PackerImpl.class; else impl = com.sun.java.util.jar.pack.UnpackerImpl.class;
            }
            return impl.newInstance();
        } catch (ClassNotFoundException e) {
            throw new Error("Class not found: " + implName + ":\ncheck property " + prop + " in your properties file.", e);
        } catch (InstantiationException e) {
            throw new Error("Could not instantiate: " + implName + ":\ncheck property " + prop + " in your properties file.", e);
        } catch (IllegalAccessException e) {
            throw new Error("Cannot access class: " + implName + ":\ncheck property " + prop + " in your properties file.", e);
        }
    }
}
