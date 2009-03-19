package mobius.logic;

import ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException;

import java.io.File;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import mobius.logic.clops.LogicSyncOptionsInterface;
import mobius.logic.clops.LogicSyncParser;
import mobius.logic.lang.ALanguage;
import mobius.logic.lang.coq.CoqLanguage;
import mobius.logic.lang.generic.GenericLanguage;
import mobius.logic.lang.nat.NaturalLanguage;

/**
 * The main class file of LogicSync.
 * It handles the arguments passed by the command line.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class Main {

  private static final String BAD_USAGE_MSG =     
     "Bad usage!\n" +
     "(try java -jar logicsync.jar -help)";
  private static final String HELP_MSG =
    "LSync Version 0.1\n" +
    "Syntax: java -jar logicync [-h] <files> [-g <file>] [-m <file>]\n" +
    "-h, -help, --help Show this help message.\n" +
    "<files>           Input file(s). Determine their type by their extension.\n" +
    "-g <file>         Generates files. Files will erase the previous version.\n" +
    "-m <file>         Merge with existing file. " +
    "If there is no previous version, creates a new file.";
  
  private final List<File> fInput;
  private final List<File> fGenerate;
  private final List<File> fMerge;
  private final Map<String, ALanguage> fLang;

  public Main(LogicSyncOptionsInterface opt, Map<String, ALanguage> list) {
    this(list, opt.getFiles(), opt.getGenerate(), opt.getMerge());
  }

  public Main(Map<String, ALanguage> list, List<File> file, List<File> generate, List<File> merge) {
    fInput = file;
    fGenerate = generate;
    fMerge = merge;
    fLang = list;
  }

  /**
   * @param args
   */
  public static void main(final String[] args) {
    LogicSyncParser parser;
    try {
      parser = new LogicSyncParser();
    } 
    catch (InvalidOptionPropertyValueException e) {
      e.printStackTrace();
      return;
    }
    if (!parser.parse(args)) {
      System.err.println(BAD_USAGE_MSG);
      return;
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
    
    final Map<String, ALanguage> list = new HashMap<String, ALanguage>();
    list.put("coq", new CoqLanguage());
    list.put("nat", new NaturalLanguage());
    list.put("gen", new GenericLanguage());
        
    final Main main = new Main(opt, list);
    main.start();

  }

  public void start() {
    initLanguages();
    
    System.out.println("1: Preparation phase");
    for (ALanguage lang: fLang.values()) {
      lang.prepare();
    }
    
    System.out.println("2: Generation phase");
    for (ALanguage lang: fLang.values()) {
      lang.generate();
    }
  }

  private void initLanguages() {
    for (File in: fInput) {
      for (ALanguage lang: fLang.values()) {
        if (lang.isLanguageFile(in)) {
          lang.addInput(in);
        }
      }    
    }
    for (File gen: fGenerate) {
      for (ALanguage lang: fLang.values()) {
        if (lang.isLanguageFile(gen)) {
          lang.addGenerate(gen);
        }
      }    
    }
    for (File merge: fMerge) {
      for (ALanguage lang: fLang.values()) {
        if (lang.isLanguageFile(merge)) {
          lang.addMerge(merge);
        }
      }    
    }
  }

}
