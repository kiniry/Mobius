package java.security.cert;

import java.io.IOException;
import sun.misc.HexDumpEncoder;
import sun.security.util.DerValue;

public class PolicyQualifierInfo {
    private byte[] mEncoded;
    private String mId;
    private byte[] mData;
    private String pqiString;
    
    public PolicyQualifierInfo(byte[] encoded) throws IOException {
        
        mEncoded = (byte[])(byte[])encoded.clone();
        DerValue val = new DerValue(mEncoded);
        if (val.tag != DerValue.tag_Sequence) throw new IOException("Invalid encoding for PolicyQualifierInfo");
        mId = (val.data.getDerValue()).getOID().toString();
        byte[] tmp = val.data.toByteArray();
        if (tmp == null) {
            mData = null;
        } else {
            mData = new byte[tmp.length];
            System.arraycopy(tmp, 0, mData, 0, tmp.length);
        }
    }
    
    public final String getPolicyQualifierId() {
        return mId;
    }
    
    public final byte[] getEncoded() {
        return (byte[])(byte[])mEncoded.clone();
    }
    
    public final byte[] getPolicyQualifier() {
        return (mData == null ? null : (byte[])(byte[])mData.clone());
    }
    
    public String toString() {
        if (pqiString != null) return pqiString;
        HexDumpEncoder enc = new HexDumpEncoder();
        StringBuffer sb = new StringBuffer();
        sb.append("PolicyQualifierInfo: [\n");
        sb.append("  qualifierID: " + mId + "\n");
        sb.append("  qualifier: " + (mData == null ? "null" : enc.encodeBuffer(mData)) + "\n");
        sb.append("]");
        pqiString = sb.toString();
        return pqiString;
    }
}
