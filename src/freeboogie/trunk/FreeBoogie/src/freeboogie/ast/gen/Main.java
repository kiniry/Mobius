/** Public domain. */

package freeboogie.ast.gen;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.logging.FileHandler;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.logging.SimpleFormatter;

import freeboogie.util.Err;

/**
 * @author rgrig
 * @author reviewed by TODO
 */
public class Main {
  private static final Logger log = Logger.getLogger("freeboogie.ast.gen");
  
  // TODO: make it possible to override this from the command line
  private static String defaultBase = "Node";

  private static Map<String, AgClass> grammar;

  // TODO: perhaps grammarFile, grammarLeftovers and readGrammarStatement
  // should be moved in a separate class
  private static BufferedReader grammarFile;
  private static StringBuilder grammarLeftovers;

  /*
   * Reads one statement from the {@code grammarFile}. The input is read line
   * by line, c++ comments are ignored, and leftovers are left in
   * {@code grammarLeftovers}. For example if the first two lines in the
   * grammar file are 
   *   // This is a short one 
   *   Program = String! name; Program <: Node; 
   * then the first call will eat the comment, return "Program = String!
   * name", and leave " Program <: Node;" in {@code grammarLeftovers}. We
   * return {@code null} when there is no more statement in the grammar. There
   * should be no subsequent call after that. We set {@code grammarLeftovers} to
   * {@code null} just to make sure erroneous calls are caught during testing.
   */
  private static String readGrammarStatement() {
    String statement = null;
    try {
      String line = null;
      int end = grammarLeftovers.indexOf(";");
      if (end == -1) {
        do {
          line = grammarFile.readLine();
          if (line == null) {
            String lo = grammarLeftovers.toString().trim();
            if (!lo.equals("")) {
              System.out.println("I'm ignoring the text at the end of the grammar:");
              System.out.println(lo);
            }
            grammarLeftovers = null;
            return null;
          }
          line = line.trim();
          if (line.startsWith("//")) continue;
          grammarLeftovers.append(' ');
          grammarLeftovers.append(line);
        } while (line.indexOf(';') == -1);
        end = grammarLeftovers.indexOf(";");
      }
      log.finest("grammarLeftovers = " + grammarLeftovers);
      log.finest("line = " + line);
      statement = grammarLeftovers.substring(0, end);
      grammarLeftovers.replace(0, end + 1, ""); // eat the semicolon
    }
    catch (IOException e) {
      Err.msg("Failed to read from grammar file.", 2);
    }
    log.fine("Read grammar statement: " + statement);
    return statement;
  }

  // @ ensures \return != null
  private static AgClass getAgClass(String clsName) {
    AgClass cls;
    if (grammar.containsKey(clsName)) cls = grammar.get(clsName);
    else {
      cls = new AgClass();
      cls.name = clsName;
      cls.base = defaultBase; 
      grammar.put(clsName, cls);
    }
    return cls;
  }

  /*
   * Reads in the file {@code fileName} and populates {@code grammar}.
   * If something is wrong in the input file warnings are written to
   * {@code System.err} but we try to be as fault tolerant as possible.
   */
  private static void parseGrammar(String fileName) {
    // open file
    try {
      grammarFile = new BufferedReader(new FileReader(fileName));
    }
    catch (IOException e) {
      System.err.println("I could not open the file " + fileName + ".");
      return;
    }
    
    grammar = new HashMap<String, AgClass>(100); 

    // read and process rule by rule
    grammarLeftovers = new StringBuilder();
    String stmt;
    while ((stmt = readGrammarStatement()) != null) {
      int lrSep;
      if ((lrSep = stmt.indexOf('=')) != -1) {
        // parse class = members
        String clsName = stmt.substring(0, lrSep).trim();
        String rhs = stmt.substring(lrSep + 1);
        String[] members = rhs.split(",");

        // identify the class or create one if none exists
        AgClass cls = getAgClass(clsName);

        // add members to the class
        for (int m = 0; m < members.length; ++m) {
          String[] tn = members[m].split("\\w+");
          if (tn.length != 2) {
            System.err.println("I'm ignoring a member of " + clsName + ":");
            System.err.println(members[m]);
            continue;
          }

          AgMember mem = new AgMember();
          mem.type = tn[0];
          mem.name = tn[1];
          if (mem.type.endsWith("!")) {
            mem.nonNull = true;
            mem.type = mem.type.substring(0, mem.type.length() - 1);
          }
          cls.members.add(mem);
        } // for - ad members to the class

      } else if ((lrSep = stmt.indexOf(":>")) != -1) {
        // parse class <: subclasses
        String baseName = stmt.substring(0, lrSep).trim();
        String rhs = stmt.substring(lrSep + 2);
        String[] derived = rhs.split(","); 
        
        for (int d = 0; d < derived.length; ++d) {
          AgClass cls = getAgClass(derived[d].trim());
          if (cls.base.equals(defaultBase)) {
            cls.base = baseName;
          } else {
            System.err.print("You gave more than one base class for ");
            System.err.print(cls.name + " (" + cls.base + " and ");
            System.err.println(baseName + ").");
            System.err.println("I'm using the latter.");
          }
        } // for - going thru the derived classes
        
      } else if ((lrSep = stmt.indexOf(':')) != -1) {
        // parse class: spec
        Err.notImplemented();
      } else {
        System.err.println("This looks strange, I'm ignoring it:");
        System.err.println(stmt);
      }
    } // while for grammar statements

    // set primitive status
    Iterator<Map.Entry<String, AgClass>> it = grammar.entrySet().iterator();
    while (it.hasNext()) {
      Map.Entry<String, AgClass> entry = it.next();
      Iterator<AgMember> mit = entry.getValue().members.iterator();
      while (mit.hasNext()) {
        AgMember m = mit.next();
        if (grammar.containsKey(m.name)) m.primitive = false;
      }
    }
  }

  private static void processTemplate(String fileName) {
    Err.notImplemented();
  }

  /**
   * Reads in a grammar file and uses that information to expand the macros in a
   * template file.
   * 
   * @param args <code>args[0]</code> is the grammar file and
   *          <code>args[1..]</code> are template files
   */
  public static void main(String[] args) {
    if (args.length == 0) Err.msg(
      "Syntax: java freeboogie.ast.gen.Main grammar templates",
      1);
    
    try {
      Handler logh = new FileHandler("ast_gen.log");
      logh.setFormatter(new SimpleFormatter());
      log.addHandler(logh);
      log.setLevel(Level.ALL); // for debug
    } catch (IOException e) {
      System.err.println("I can't create a log file. Nevermind.");
    }

    parseGrammar(args[0]);
    for (int t = 1; t < args.length; ++t)
      processTemplate(args[t]);
  }
}
