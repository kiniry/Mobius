package mobius.cct.tools.merge;

import mobius.cct.tools.AbstractTool;
import mobius.cct.tools.Environment;

/**
 * A tool which merges a certificate file with class.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class MergeTool extends AbstractTool {
  /**
   * Entry point.
   * @param env Environment.
   */
  @Override
  public void main(final Environment env) {
    env.getErr().println(
      getMessage("merge.error.not.implemented", env)
    );
  }

}
