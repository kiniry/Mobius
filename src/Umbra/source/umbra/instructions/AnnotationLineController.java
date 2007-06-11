package umbra.instructions;


/**
 * This is a class that contains some information
 * TODO
 *
 * @author Wojciech Wąs
 */
public class AnnotationLineController extends BytecodeLineController {

  /**
   * This constructor remembers the line with the BML
   * annotations only.
   *
   * @param l the line with the BML annotations
   */
  public AnnotationLineController(String l) {
    super(l);
  }

  /**
   * @see BytecodeLineController#correct()
   */
  public boolean correct()
  {
    return true;
  }
}
