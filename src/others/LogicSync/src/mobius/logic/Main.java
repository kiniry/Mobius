package mobius.logic;

import ie.ucd.clops.runtime.automaton.AutomatonException;
import ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException;
import ie.ucd.clops.runtime.options.InvalidOptionValueException;
import ie.ucd.clops.util.OptionUtil;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import mobius.logic.clops.LogicSyncOptionsInterface;
import mobius.logic.clops.LogicSyncParser;
import mobius.logic.lang.ALanguage;
import mobius.logic.lang.generic.GenericLanguage;
import mobius.logic.lang.generic.TypeChecker;
import mobius.logic.lang.generic.ast.GenericAst;
import mobius.logic.lang.generic.ast.TypeCheckedAst;
import mobius.util.ClassUtils;
import mobius.util.Logger;

/**
 * The main class file of LogicSync.
 * It handles the arguments passed by the command line.
 * 
 * @author J. Charles (julien.charles@gmail.com)
 */
public class Main {

  /** Welcome message: "LSync Version 0.1". */
  private static final String WELCOME_MSG = "LSync Version 0.1";
  
  /** the bad usage message. */
  private static final String BAD_USAGE_MSG =
     "Bad usage!\n" +
     "(try java -jar logicsync.jar -help)";
  
  /** the help message used when the argument help is specified. */
  private static final String HELP_MSG_START =
    "Syntax: java -jar logicsync [-h] <files> [-g <file>] [-m <file>]\n";
  
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

  private boolean fTypeCheck;
  
  
  public Main(LogicSyncOptionsInterface opt, Map<ALanguage, String> list) {
    this(list, opt.isTypeCheckSet(), opt.getFiles(), opt.getGenerate(), opt.getMerge());
  }

  public Main(Map<ALanguage, String> list, boolean typeCheck, List<File> file, List<File> generate, List<File> merge) {
    fTypeCheck = typeCheck;
    fInput = file;
    fGenerate = generate;
    fMerge = merge;
    fLang = list;
  }

  /**
   * @param args The program arguments
   */
  public static void main(final String[] args) {
    Logger.out.println(WELCOME_MSG);
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
        Logger.err.println(BAD_USAGE_MSG);
        return;
      }
    } 
    catch (AutomatonException e) {
      e.printStackTrace();
    }
    catch (InvalidOptionValueException e) {
      e.printStackTrace();
    }
    
    final LogicSyncOptionsInterface opt = parser.getOptionStore();
    if (opt.isHelpSet()) {
      Logger.out.println(HELP_MSG_START);
      OptionUtil.printOptions(Logger.out, parser.getOptionStore().getOptionsWithoutErrorOption(), 80, 2);
      return;
    }
    
    if (!opt.isFilesSet()) {
      Logger.err.println("I need at least one input file!");
      Logger.err.println(BAD_USAGE_MSG);
      return;
    }    
    
    final Map<ALanguage, String> list = new HashMap<ALanguage, String>();
    
    try {
      final List<Class<ALanguage>> l = 
        ClassUtils.getClasses("mobius.logic.lang", ALanguage.class);
      instanciate(list, l);
    } 
    catch (ClassNotFoundException e) {
      e.printStackTrace();
    } 
    catch (IOException e) {
      e.printStackTrace();
    }
    final ALanguage gen = new GenericLanguage(); 
    list.put(gen, gen.getName());
    Logger.out.print("Using languages:");
    for (String name: list.values()) {
      Logger.out.print(" " + name);
    }
    Logger.out.println(".\n");
    final Main main = new Main(opt, list);
    main.start();

  }

  /**
   * Instanciate the classes of the list, and put the result
   * into a map.
   * @param map the result of the instanciation
   * @param l the list of classes to instanciate
   */
  private static void instanciate(final Map<ALanguage, String> map, 
                                  final List<Class<ALanguage>> l) {
    final List<Class<ALanguage>> filtered = filter(l);
    for (Class< ? > c: filtered) {
      try {
        final ALanguage al = (ALanguage)c.newInstance();
        map.put(al, al.getName());
      } 
      catch (InstantiationException e) {
        Logger.err.println("The language " + c.getName() + " cannot be " +
                           "instanciated... Maybe it is abstract?");
      } 
      catch (IllegalAccessException e) {
        Logger.err.println("The language " + c.getName() + " doesn't have " +
                           "a public constructor which is strange.");
      }

    }
  }

  /**
   * What we don't want: mobius.logic.lang.* classes
   * And the generic language.
   * @param l the list to purge
   * @return the list without the offuscing classes
   */
  private static <C> List<Class<C>> filter(final List<Class<C>> l) {
    final List<Class<C>> res = new ArrayList<Class<C>>();
    for (Class<C> c: l) {
      final String pkg = c.getPackage().getName(); 
      if (!pkg.equals("mobius.logic.lang") &&
          !pkg.equals("mobius.logic.lang.generic")) {
        res.add(c);
      }
    }
    return res;
  }

  public void start() {
    initLanguages();
    
    Logger.out.println("\n1: Preparation phase");
    for (ALanguage lang: fLang.keySet()) {
      lang.prepare();
    }
    
    Logger.out.println("\n2: Consistency check phase");
    /* if there is more that 1 language input we do the check */
    if (fInputLanguages.size() > 1) {
      // right now triggers an error
      Logger.out.println("Couldn't check consistency between these languages: " + 
                         fLang.values() + 
                         "\nNo consistency check :( sorry.");
      Logger.out.println("I am unhappy about that but I am extracting from " +
                         "the first language I find :P\n" +
                         "Namely: " + fInputLanguages.iterator().next() + ".");
    }
    
    final GenericAst ast = fInputLanguages.iterator().next().extractGenericAst();

    final TypeChecker tc = new TypeChecker(ast);

    Logger.out.print("TypeChecking...");
    if (tc.check()) {
      Logger.out.println(" done.");
    }
    else {
      Logger.out.println(" FAILED miserably!");
      tc.printDetailedResults();
      return;
    }
    if (fTypeCheck) {
      tc.printDetailedResults();
    }
    final TypeCheckedAst tcAst = new TypeCheckedAst(tc, ast);
    
    
    Logger.out.println("\n3: Generation phase");
    for (ALanguage lang: fGenerateLanguages) {
      lang.generateFrom(tcAst);
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

