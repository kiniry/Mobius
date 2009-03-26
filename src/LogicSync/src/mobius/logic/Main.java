package mobius.logic;

import ie.ucd.clops.runtime.automaton.AutomatonException;
import ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException;
import ie.ucd.clops.runtime.options.InvalidOptionValueException;

import java.io.File;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import mobius.logic.clops.LogicSyncOptionsInterface;
import mobius.logic.clops.LogicSyncParser;
import mobius.logic.lang.ALanguage;
import mobius.logic.lang.coq.CoqLanguage;
import mobius.logic.lang.generic.GenericLanguage;
import mobius.logic.lang.generic.ast.GenericAst;
import mobius.logic.lang.nat.NaturalLanguage;

/**
 * The main class file of LogicSync.
 * It handles the arguments passed by the command line.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class Main {

  /** Welcome message: "LSync Version 0.1". */
  private static final String WELCOME_MSG = "LSync Version 0.1";
  
  /** the bad usage message. */
  private static final String BAD_USAGE_MSG =
     "Bad usage!\n" +
     "(try java -jar logicsync.jar -help)";
  
  /** the help message used when the argument help is specified. */
  private static final String HELP_MSG =
    "Syntax: java -jar logicsync [-h] <files> [-g <file>] [-m <file>]\n" +
    "-h, -help, --help Show this help message.\n" +
    "<files>           Input file(s). Determine their type by their extension.\n" +
    "-g <file>         Generates files. Files will erase the previous version.\n" +
    "-m <file>         Merge with existing file. " +
    "If there is no previous version, creates a new file.";
  
  /** the list of input files. */
  private final List<File> fInput;
  
  /** the list of files to generate. */
  private final List<File> fGenerate;
  
  /** the list of files to merge. */
  private final List<File> fMerge;
  
  /** the current list of languages. */
  private final Map<ALanguage, String> fLang;
  
  /** the list of the language that have a specified input. */
  private Set<ALanguage> fInputLanguages = new HashSet<ALanguage>();

  /** the list of the language that will have to generate to an output. */
  private Set<ALanguage> fGenerateLanguages = new HashSet<ALanguage>();
  
  /** the list of the language that will have to merge to an output. */
  private Set<ALanguage> fMergeLanguages = new HashSet<ALanguage>();
  
  
  public Main(LogicSyncOptionsInterface opt, Map<ALanguage, String> list) {
    this(list, opt.getFiles(), opt.getGenerate(), opt.getMerge());
  }

  public Main(Map<ALanguage, String> list, List<File> file, List<File> generate, List<File> merge) {
    fInput = file;
    fGenerate = generate;
    fMerge = merge;
    fLang = list;
  }

  /**
   * @param args
   */
  public static void main(final String[] args) {
    System.out.println(WELCOME_MSG);
    LogicSyncParser parser;
    try {
      parser = new LogicSyncParser();
    } 
    catch (InvalidOptionPropertyValueException e) {
      e.printStackTrace();
      return;
    }
    try {
      if (!parser.parse(args)) {
        System.err.println(BAD_USAGE_MSG);
        return;
      }
    } 
    catch (AutomatonException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
    catch (InvalidOptionValueException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }
    
    final LogicSyncOptionsInterface opt = parser.getOptionStore();
    if (opt.isHelpSet()) {
      System.err.println(HELP_MSG);
      return;
    }
    
    if (!opt.isFilesSet()) {
      System.err.println("I need at least one input file!");
      System.err.println(BAD_USAGE_MSG);
      return;
    }    
    
    final Map<ALanguage, String> list = new HashMap<ALanguage, String>();
    list.put(new CoqLanguage(), "Coq");
    list.put(new NaturalLanguage(), "Natural");
    list.put(new GenericLanguage(), "Generic");
        
    final Main main = new Main(opt, list);
    main.start();

  }

  public void start() {
    initLanguages();
    
    System.out.println("\n1: Preparation phase");
    for (ALanguage lang: fLang.keySet()) {
      lang.prepare();
    }
    
    System.out.println("\n2: Consistency check phase");
    /* if there is more that 1 language input we do the check */
    if (fInputLanguages.size() > 1) {
      // right now triggers an error
      System.out.println("Couldn't check consistency between these languages: " + 
                         fLang.values() + 
                         "\nNo consistency check :( sorry.");
      System.out.println("I am unhappy about that but I am extracting from " +
                         "the first language I find :P\n" +
                         "Namely: " + fInputLanguages.iterator().next() + ".");
    }
    
    final GenericAst ast = fInputLanguages.iterator().next().extractGenericAst();
    
    System.out.println("\n3: Generation phase");
    for (ALanguage lang: fGenerateLanguages) {
      lang.generateFrom(ast);
    }
    for (ALanguage lang: fMergeLanguages) {
      lang.mergeWith(ast);
    }
  }

  private void initLanguages() {
    for (File in: fInput) {
      for (ALanguage lang: fLang.keySet()) {
        if (lang.isLanguageFile(in)) {
          lang.addInput(in);
          fInputLanguages .add(lang);
        }
      }    
    }
    for (File gen: fGenerate) {
      for (ALanguage lang: fLang.keySet()) {
        if (lang.isLanguageFile(gen)) {
          lang.addGenerate(gen);
          fGenerateLanguages.add(lang);
        }
      }    
    }
    for (File merge: fMerge) {
      for (ALanguage lang: fLang.keySet()) {
        if (lang.isLanguageFile(merge)) {
          lang.addMerge(merge);
          fMergeLanguages.add(lang);
        }
      }    
    }
  }

}
