package bmllib.utils;

public class NumberUtils {

  public static final int INTEGER_IN_BYTES = Integer.SIZE / Byte.SIZE;
  
  public static final int THREE_BYTES_SIZE = Byte.SIZE * 3;
  
  public static final int TWO_BYTES_SIZE = Byte.SIZE * 2;
  
  public static final int ONE_BYTE_SIZE = Byte.SIZE;
  
  public static final int LOWEST_BYTE_MASK = 0xFF;

  /**
   * The base power for decimal numbers.
   */
  public static final int DECIMAL_RADIX = 10;

  /**
   * The maximal number of spaces to be inserted as padding in front of
   * a number.
   */
  private static final int MAXIMAL_PADDING = 2;

  /**
   * This method returns the given number with an initial padding which
   * depends on the size of the number. We assume that the highest number
   * has at most {@link MAXIMAL_PADDING} + 1 digits. The padding is at most
   * {@link #MAXIMAL_PADDING}. In case the number has more digits no
   * padding is generated
   *
   * @param num the number to be padded
   * @return
   */
  public static String paddedNumber(final int num) {
    int acc = num;
    int pow = 0;
    while (acc > 0) {
      pow++;
      acc = acc / DECIMAL_RADIX;
    }
    if (pow > MAXIMAL_PADDING) {
      return Integer.toString(num);
    }
    StringBuffer ret = new StringBuffer(pow);
    for (int  i = pow - 1; i >= 0; i--) {
      ret.insert(i, ' ');
    }
    return ret.append(num).toString();
  }
}
