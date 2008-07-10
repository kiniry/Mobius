package mobius.cct.tests.testutil;

import java.io.IOException;
import java.io.InputStream;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;

/**
 * Static helper functions used by tests.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class Util {
  /**
   * MD5 digest name.
   */
  public static final String MD5 = "MD5";
  /**
   * SHA1 digest name.
   */
  public static final String SHA1 = "SHA1";
  
  /**
   * Size of buffers used to read streams.
   */
  private static final int BUFFER_SIZE = 4096;
  
  /**
   * Hex digits.
   */
  private static final String[] digits = 
    {"0","1","2","3","4","5","6","7","8", "9", 
     "a", "b", "c", "d", "e", "f"};
  
  /**
   * Calculate digest from all bytes in given stream.
   * @param is Input stream.
   * @param alg Digest algorithm.
   * @return Digest.
   * @throws NoSuchAlgorithmException .
   * @throws IOException .
   */
  public static byte[] digest(final InputStream is, 
                              final String alg) 
      throws NoSuchAlgorithmException, IOException {
    MessageDigest d = MessageDigest.getInstance(alg);
    byte b[] = new byte[BUFFER_SIZE];
    int l;
    
    while ((l = is.read(b)) > 0) {
      d.update(b, 0, l);
    }
    return d.digest();
  }
  
  /**
   * Convert byte to hex string. The string has
   * always 2 characters (it is padded with a zero if necessary).
   * @param b Byte value.
   * @return Hex string.
   */
  public static String toHex(byte b) {
    return digits[(b >>> 4) & 0xf] + digits[b & 0xf];
  }
  
  /**
   * Convert byte array to hex string.
   * @param b Array.
   * @return Hex string.
   */
  public static String toHex(byte[] b) {
    int i;
    
    StringBuilder sb = new StringBuilder();
    for (i = 0; i < b.length; i++) {
      sb.append(toHex(b[i]));
    }
    return sb.toString();
  }
}
