package java.awt.datatransfer;

import java.io.*;
import java.nio.*;
import java.util.*;
import sun.awt.datatransfer.DataTransferer;

public class DataFlavor implements Externalizable, Cloneable {
    private static final long serialVersionUID = 8367026044764648243L;
    private static final Class ioInputStreamClass = InputStream.class;
    
    protected static final Class tryToLoadClass(String className, ClassLoader fallback) throws ClassNotFoundException {
        ClassLoader systemClassLoader = (ClassLoader)(ClassLoader)java.security.AccessController.doPrivileged(new DataFlavor$1());
        try {
            return Class.forName(className, true, systemClassLoader);
        } catch (ClassNotFoundException e2) {
            if (fallback != null) {
                return Class.forName(className, true, fallback);
            } else {
                throw new ClassNotFoundException(className);
            }
        }
    }
    
    private static DataFlavor createConstant(Class rc, String prn) {
        try {
            return new DataFlavor(rc, prn);
        } catch (Exception e) {
            return null;
        }
    }
    
    private static DataFlavor createConstant(String mt, String prn) {
        try {
            return new DataFlavor(mt, prn);
        } catch (Exception e) {
            return null;
        }
    }
    public static final DataFlavor stringFlavor = createConstant(String.class, "Unicode String");
    public static final DataFlavor imageFlavor = createConstant("image/x-java-image; class=java.awt.Image", "Image");
    
    public static final DataFlavor plainTextFlavor = createConstant("text/plain; charset=unicode; class=java.io.InputStream", "Plain Text");
    public static final String javaSerializedObjectMimeType = "application/x-java-serialized-object";
    public static final DataFlavor javaFileListFlavor = createConstant("application/x-java-file-list;class=java.util.List", null);
    public static final String javaJVMLocalObjectMimeType = "application/x-java-jvm-local-objectref";
    public static final String javaRemoteObjectMimeType = "application/x-java-remote-object";
    
    public DataFlavor() {
        
    }
    
    private DataFlavor(String primaryType, String subType, MimeTypeParameterList params, Class representationClass, String humanPresentableName) {
        
        if (primaryType == null) {
            throw new NullPointerException("primaryType");
        }
        if (subType == null) {
            throw new NullPointerException("subType");
        }
        if (representationClass == null) {
            throw new NullPointerException("representationClass");
        }
        if (params == null) params = new MimeTypeParameterList();
        params.set("class", representationClass.getName());
        if (humanPresentableName == null) {
            humanPresentableName = (String)params.get("humanPresentableName");
            if (humanPresentableName == null) humanPresentableName = primaryType + "/" + subType;
        }
        try {
            mimeType = new MimeType(primaryType, subType, params);
        } catch (MimeTypeParseException mtpe) {
            throw new IllegalArgumentException("MimeType Parse Exception: " + mtpe.getMessage());
        }
        this.representationClass = representationClass;
        this.humanPresentableName = humanPresentableName;
        mimeType.removeParameter("humanPresentableName");
    }
    
    public DataFlavor(Class representationClass, String humanPresentableName) {
        this("application", "x-java-serialized-object", null, representationClass, humanPresentableName);
        if (representationClass == null) {
            throw new NullPointerException("representationClass");
        }
    }
    
    public DataFlavor(String mimeType, String humanPresentableName) {
        
        if (mimeType == null) {
            throw new NullPointerException("mimeType");
        }
        try {
            initialize(mimeType, humanPresentableName, this.getClass().getClassLoader());
        } catch (MimeTypeParseException mtpe) {
            throw new IllegalArgumentException("failed to parse:" + mimeType);
        } catch (ClassNotFoundException cnfe) {
            throw new IllegalArgumentException("can\'t find specified class: " + cnfe.getMessage());
        }
    }
    
    public DataFlavor(String mimeType, String humanPresentableName, ClassLoader classLoader) throws ClassNotFoundException {
        
        if (mimeType == null) {
            throw new NullPointerException("mimeType");
        }
        try {
            initialize(mimeType, humanPresentableName, classLoader);
        } catch (MimeTypeParseException mtpe) {
            throw new IllegalArgumentException("failed to parse:" + mimeType);
        }
    }
    
    public DataFlavor(String mimeType) throws ClassNotFoundException {
        
        if (mimeType == null) {
            throw new NullPointerException("mimeType");
        }
        try {
            initialize(mimeType, null, this.getClass().getClassLoader());
        } catch (MimeTypeParseException mtpe) {
            throw new IllegalArgumentException("failed to parse:" + mimeType);
        }
    }
    
    private void initialize(String mimeType, String humanPresentableName, ClassLoader classLoader) throws MimeTypeParseException, ClassNotFoundException {
        if (mimeType == null) {
            throw new NullPointerException("mimeType");
        }
        this.mimeType = new MimeType(mimeType);
        String rcn = getParameter("class");
        if (rcn == null) {
            if ("application/x-java-serialized-object".equals(this.mimeType.getBaseType())) throw new IllegalArgumentException("no representation class specified for:" + mimeType); else representationClass = InputStream.class;
        } else {
            representationClass = DataFlavor.tryToLoadClass(rcn, classLoader);
        }
        this.mimeType.setParameter("class", representationClass.getName());
        if (humanPresentableName == null) {
            humanPresentableName = this.mimeType.getParameter("humanPresentableName");
            if (humanPresentableName == null) humanPresentableName = this.mimeType.getPrimaryType() + "/" + this.mimeType.getSubType();
        }
        this.humanPresentableName = humanPresentableName;
        this.mimeType.removeParameter("humanPresentableName");
    }
    
    public String toString() {
        String string = getClass().getName();
        string += "[" + paramString() + "]";
        return string;
    }
    
    private String paramString() {
        String params = "";
        params += "mimetype=";
        if (mimeType == null) {
            params += "null";
        } else {
            params += mimeType.getBaseType();
        }
        params += ";representationclass=";
        if (representationClass == null) {
            params += "null";
        } else {
            params += representationClass.getName();
        }
        if (DataTransferer.isFlavorCharsetTextType(this) && (isRepresentationClassInputStream() || isRepresentationClassByteBuffer() || DataTransferer.byteArrayClass.equals(representationClass))) {
            params += ";charset=" + DataTransferer.getTextCharset(this);
        }
        return params;
    }
    
    public static final DataFlavor getTextPlainUnicodeFlavor() {
        String encoding = null;
        DataTransferer transferer = DataTransferer.getInstance();
        if (transferer != null) {
            encoding = transferer.getDefaultUnicodeEncoding();
        }
        return new DataFlavor("text/plain;charset=" + encoding + ";class=java.io.InputStream", "Plain Text");
    }
    
    public static final DataFlavor selectBestTextFlavor(DataFlavor[] availableFlavors) {
        if (availableFlavors == null || availableFlavors.length == 0) {
            return null;
        }
        if (textFlavorComparator == null) {
            textFlavorComparator = new DataFlavor$TextFlavorComparator();
        }
        DataFlavor bestFlavor = (DataFlavor)(DataFlavor)Collections.max(Arrays.asList(availableFlavors), textFlavorComparator);
        if (!bestFlavor.isFlavorTextType()) {
            return null;
        }
        return bestFlavor;
    }
    private static Comparator textFlavorComparator;
    {
    }
    
    public Reader getReaderForText(Transferable transferable) throws UnsupportedFlavorException, IOException {
        Object transferObject = transferable.getTransferData(this);
        if (transferObject == null) {
            throw new IllegalArgumentException("getTransferData() returned null");
        }
        if (transferObject instanceof Reader) {
            return (Reader)(Reader)transferObject;
        } else if (transferObject instanceof String) {
            return new StringReader((String)(String)transferObject);
        } else if (transferObject instanceof CharBuffer) {
            CharBuffer buffer = (CharBuffer)(CharBuffer)transferObject;
            int size = buffer.remaining();
            char[] chars = new char[size];
            buffer.get(chars, 0, size);
            return new CharArrayReader(chars);
        } else if (transferObject instanceof char[]) {
            return new CharArrayReader((char[])(char[])transferObject);
        }
        InputStream stream = null;
        if (transferObject instanceof InputStream) {
            stream = (InputStream)(InputStream)transferObject;
        } else if (transferObject instanceof ByteBuffer) {
            ByteBuffer buffer = (ByteBuffer)(ByteBuffer)transferObject;
            int size = buffer.remaining();
            byte[] bytes = new byte[size];
            buffer.get(bytes, 0, size);
            stream = new ByteArrayInputStream(bytes);
        } else if (transferObject instanceof byte[]) {
            stream = new ByteArrayInputStream((byte[])(byte[])transferObject);
        }
        if (stream == null) {
            throw new IllegalArgumentException("transfer data is not Reader, String, CharBuffer, char array, InputStream, ByteBuffer, or byte array");
        }
        String encoding = getParameter("charset");
        return (encoding == null) ? new InputStreamReader(stream) : new InputStreamReader(stream, encoding);
    }
    
    public String getMimeType() {
        return (mimeType != null) ? mimeType.toString() : null;
    }
    
    public Class getRepresentationClass() {
        return representationClass;
    }
    
    public String getHumanPresentableName() {
        return humanPresentableName;
    }
    
    public String getPrimaryType() {
        return (mimeType != null) ? mimeType.getPrimaryType() : null;
    }
    
    public String getSubType() {
        return (mimeType != null) ? mimeType.getSubType() : null;
    }
    
    public String getParameter(String paramName) {
        if (paramName.equals("humanPresentableName")) {
            return humanPresentableName;
        } else {
            return (mimeType != null) ? mimeType.getParameter(paramName) : null;
        }
    }
    
    public void setHumanPresentableName(String humanPresentableName) {
        this.humanPresentableName = humanPresentableName;
    }
    
    public boolean equals(Object o) {
        return ((o instanceof DataFlavor) && equals((DataFlavor)(DataFlavor)o));
    }
    
    public boolean equals(DataFlavor that) {
        if (that == null) {
            return false;
        }
        if (this == that) {
            return true;
        }
        if (representationClass == null) {
            if (that.getRepresentationClass() != null) {
                return false;
            }
        } else {
            if (!representationClass.equals(that.getRepresentationClass())) {
                return false;
            }
        }
        if (mimeType == null) {
            if (that.mimeType != null) {
                return false;
            }
        } else {
            if (!mimeType.match(that.mimeType)) {
                return false;
            }
            if ("text".equals(getPrimaryType()) && DataTransferer.doesSubtypeSupportCharset(this) && representationClass != null && !(isRepresentationClassReader() || String.class.equals(representationClass) || isRepresentationClassCharBuffer() || DataTransferer.charArrayClass.equals(representationClass))) {
                String thisCharset = DataTransferer.canonicalName(getParameter("charset"));
                String thatCharset = DataTransferer.canonicalName(that.getParameter("charset"));
                if (thisCharset == null) {
                    if (thatCharset != null) {
                        return false;
                    }
                } else {
                    if (!thisCharset.equals(thatCharset)) {
                        return false;
                    }
                }
            }
        }
        return true;
    }
    
    
    public boolean equals(String s) {
        if (s == null || mimeType == null) return false;
        return isMimeTypeEqual(s);
    }
    
    public int hashCode() {
        int total = 0;
        if (representationClass != null) {
            total += representationClass.hashCode();
        }
        if (mimeType != null) {
            String primaryType = mimeType.getPrimaryType();
            if (primaryType != null) {
                total += primaryType.hashCode();
            }
            if ("text".equals(primaryType) && DataTransferer.doesSubtypeSupportCharset(this) && representationClass != null && !(isRepresentationClassReader() || String.class.equals(representationClass) || isRepresentationClassCharBuffer() || DataTransferer.charArrayClass.equals(representationClass))) {
                String charset = DataTransferer.canonicalName(getParameter("charset"));
                if (charset != null) {
                    total += charset.hashCode();
                }
            }
        }
        return total;
    }
    
    public boolean match(DataFlavor that) {
        return equals(that);
    }
    
    public boolean isMimeTypeEqual(String mimeType) {
        if (mimeType == null) {
            throw new NullPointerException("mimeType");
        }
        if (this.mimeType == null) {
            return false;
        }
        try {
            return this.mimeType.match(new MimeType(mimeType));
        } catch (MimeTypeParseException mtpe) {
            return false;
        }
    }
    
    public final boolean isMimeTypeEqual(DataFlavor dataFlavor) {
        return isMimeTypeEqual(dataFlavor.mimeType);
    }
    
    private boolean isMimeTypeEqual(MimeType mtype) {
        if (this.mimeType == null) {
            return (mtype == null);
        }
        return mimeType.match(mtype);
    }
    
    public boolean isMimeTypeSerializedObject() {
        return isMimeTypeEqual(javaSerializedObjectMimeType);
    }
    
    public final Class getDefaultRepresentationClass() {
        return ioInputStreamClass;
    }
    
    public final String getDefaultRepresentationClassAsString() {
        return getDefaultRepresentationClass().getName();
    }
    
    public boolean isRepresentationClassInputStream() {
        return ioInputStreamClass.isAssignableFrom(representationClass);
    }
    
    public boolean isRepresentationClassReader() {
        return Reader.class.isAssignableFrom(representationClass);
    }
    
    public boolean isRepresentationClassCharBuffer() {
        return CharBuffer.class.isAssignableFrom(representationClass);
    }
    
    public boolean isRepresentationClassByteBuffer() {
        return ByteBuffer.class.isAssignableFrom(representationClass);
    }
    
    public boolean isRepresentationClassSerializable() {
        return Serializable.class.isAssignableFrom(representationClass);
    }
    
    public boolean isRepresentationClassRemote() {
        return java.rmi.Remote.class.isAssignableFrom(representationClass);
    }
    
    public boolean isFlavorSerializedObjectType() {
        return isRepresentationClassSerializable() && isMimeTypeEqual(javaSerializedObjectMimeType);
    }
    
    public boolean isFlavorRemoteObjectType() {
        return isRepresentationClassRemote() && isRepresentationClassSerializable() && isMimeTypeEqual(javaRemoteObjectMimeType);
    }
    
    public boolean isFlavorJavaFileListType() {
        if (mimeType == null || representationClass == null) return false;
        return List.class.isAssignableFrom(representationClass) && mimeType.match(javaFileListFlavor.mimeType);
    }
    
    public boolean isFlavorTextType() {
        return (DataTransferer.isFlavorCharsetTextType(this) || DataTransferer.isFlavorNoncharsetTextType(this));
    }
    
    public synchronized void writeExternal(ObjectOutput os) throws IOException {
        if (mimeType != null) {
            mimeType.setParameter("humanPresentableName", humanPresentableName);
            os.writeObject(mimeType);
            mimeType.removeParameter("humanPresentableName");
        } else {
            os.writeObject(null);
        }
        os.writeObject(representationClass);
    }
    
    public synchronized void readExternal(ObjectInput is) throws IOException, ClassNotFoundException {
        String rcn = null;
        mimeType = (MimeType)(MimeType)is.readObject();
        if (mimeType != null) {
            humanPresentableName = mimeType.getParameter("humanPresentableName");
            mimeType.removeParameter("humanPresentableName");
            rcn = mimeType.getParameter("class");
            if (rcn == null) {
                throw new IOException("no class parameter specified in: " + mimeType);
            }
        }
        try {
            representationClass = (Class)(Class)is.readObject();
        } catch (OptionalDataException ode) {
            if (!ode.eof || ode.length != 0) {
                throw ode;
            }
            if (rcn != null) {
                representationClass = DataFlavor.tryToLoadClass(rcn, getClass().getClassLoader());
            }
        }
    }
    
    public Object clone() throws CloneNotSupportedException {
        Object newObj = super.clone();
        if (mimeType != null) {
            ((DataFlavor)(DataFlavor)newObj).mimeType = (MimeType)(MimeType)mimeType.clone();
        }
        return newObj;
    }
    
    
    protected String normalizeMimeTypeParameter(String parameterName, String parameterValue) {
        return parameterValue;
    }
    
    
    protected String normalizeMimeType(String mimeType) {
        return mimeType;
    }
    transient int atom;
    MimeType mimeType;
    private String humanPresentableName;
    private Class representationClass;
}
