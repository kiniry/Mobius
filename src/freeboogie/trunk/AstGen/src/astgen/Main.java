package astgen;

import java.io.*;
import java.util.HashMap;
import java.util.logging.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;


import genericutils.Err;

/**
 * The entry point of the AST generator. The usage is:
 * <pre>java astgen.Main [-b defaultBase] grammar templates</pre>.
 * 
 * @author rgrig
 */
public final class Main {
  private static final Logger log = Logger.getLogger("astgen");
  
  private static String defaultBase = "Ast";

  private Main() { /* forbid instantiation */ }

  /**
   * Reads in a grammar file and uses that information to expand the macros in a
   * template file.
   * 
   * @param args <code>args[0]</code> is the grammar file and
   *          <code>args[1..]</code> are template files
   */
  public static void main(String[] args) {
    // Setup logging.
    try {
      Handler logh = new FileHandler("ast_gen.log");
      logh.setFormatter(new SimpleFormatter());
      log.addHandler(logh);
      log.setUseParentHandlers(false);
      log.setLevel(Level.WARNING); // for release
      //log.setLevel(Level.ALL); // for debug
    } catch (IOException e) {
      System.err.println("I can't create a log file. Nevermind.");
    }
    
    int arg_idx = 0;
    Grammar grammar = null;

    HashMap<String, String> userDefs = new HashMap<String, String>(23);
    if (arg_idx < args.length && args[arg_idx].equals("-b")) {
      if (++arg_idx == args.length)
        Err.fatal("You must give a default base name after '-b'");
      defaultBase = args[arg_idx++];
      userDefs.put("defaultBaseName", defaultBase);
    }

    Pattern dp = Pattern.compile("-D(\\w*)=(.*)");
    while (arg_idx < args.length) {
      Matcher m = dp.matcher(args[arg_idx]);
      if (!m.matches()) break;
      userDefs.put(m.group(1), m.group(2));
      ++arg_idx;
    }

    if (arg_idx == args.length) { 
      Err.fatal("Syntax: java astgen.Main" 
        + " [-b defaultBaseName] (-Dkey=value)* grammar templates", 1);
    }
    
    // read the grammar
    try {
      AgParser agParser = new AgParser();
      agParser.setInputStream(new FileInputStream(args[arg_idx++]));
      agParser.parseAg();
      grammar = agParser.getGrammar();
      grammar.makeConsistent(defaultBase);
      grammar.userDefs = userDefs;
    } catch (IOException e) {
      Err.fatal("I can't read the abstract grammar from " 
        + args[arg_idx-1] + ".", 2);
    }

    for (; arg_idx < args.length; ++arg_idx) {
      // process a template
      try {
        TemplateParser template = new TemplateParser(args[arg_idx]);
        template.process(grammar);
      } catch (FileNotFoundException e) {
        Err.error("I can't find " + args[arg_idx] + 
          ". I'll skip this template.");
      } catch (IOException e) {
        Err.error("I couldn't process (completely) template " + args[arg_idx]);
      }
    }
  }
}
