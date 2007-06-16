/*
 * Created on 2005-05-14
 *
 */
package umbra.editor;

/**
 * This class is a static container that keeps the value of current coloring
 * style that is obtained after each refreshing (which takes place when
 * a bytecode document is created too).
 *
 * @author Wojtek Wąs
 */
public class Composition {

  /**
   * The current value of the colouring style.
   */
  private static int mod = 1;

  /**
   * TODO
   */
  private static boolean disas = false;

  /**
   * @return if called during disassembling - the current
   * coloring style value;
   * otherwise - it means that bytecode editor is open
   * with no relation to the source, therefore it is colored grey.
   * TODO really?
   */
  public static int getMod() {
    if (!disas) return IColorValues.MODELS.length -1;
    return mod;
  }

  /**
   * This method sets the current initial colouring style.
   */
  public static void setMod(final int i) {
    mod = i;
  }

  /**
   * TODO strange???
   */
  public static void startDisas() {
    disas = true;
  }

  /**
   * TODO
   */
  public static void stopDisas() {
    disas = false;
  }

}
