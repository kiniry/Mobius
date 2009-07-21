package mobius.cct.tools.help;

import java.io.PrintStream;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;

import mobius.cct.tools.AbstractTool;
import mobius.cct.tools.Environment;
import mobius.cct.tools.Tool;

/**
 * A tool that prints descriptions of other tools.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class HelpTool extends AbstractTool {
  /**
   * Map of tools.
   */
  private final Map<String, Tool> fTools;
  
  /**
   * Constructor.
   * @param tools Map of tools.
   */
  public HelpTool(final Map<String, Tool> tools) {
    fTools = tools;
  }

  /**
   * Entry point.
   * @param env Environment.
   */
  public void main(final Environment env) {
    final PrintStream stdout = env.getOutput();
    final String[] names = new String[fTools.size()];
    final String[] descriptions = new String[fTools.size()];
    int maxlen = 0;
    int j = 0;
    stdout.println(getMessage("help.header", env));
    final Iterator<Entry<String, Tool>> i = 
      fTools.entrySet().iterator();
    while (i.hasNext()) {
      final Entry<String, Tool> e = i.next();
      names[j] = e.getKey();
      descriptions[j] = e.getValue().getDescription(env);
      if (names[j].length() > maxlen) {
        maxlen = names[j].length();
      }
      j++;
    }
    for (j = 0; j < names.length; j++) {
      stdout.print("   ");
      stdout.print(names[j]);
      for (int k = maxlen - names[j].length(); k > 0; k--) {
        stdout.print(' ');
      }
      stdout.print(" - ");
      stdout.print(descriptions[j]);
      stdout.println();
    }
  }
  
}
