package mobius.logic;

import ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException;

import java.io.File;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import mobius.logic.clops.LogicSyncOptionsInterface;
import mobius.logic.clops.LogicSyncParser;
import mobius.logic.lang.ILanguage;
import mobius.logic.lang.coq.CoqLanguage;
import mobius.logic.lang.generic.GenericLanguage;
import mobius.logic.lang.nat.NaturalLanguage;

public class Main {

  private static final String BAD_USAGE_MSG =     
     "Bad usage!\n" +
     "(try java -jar logicsync.jar -help)";
  
  private final List<File> fInput;
  private final List<File> fGenerate;
  private final List<File> fMerge;
  private final Map<String, ILanguage> fLang;

  public Main(LogicSyncOptionsInterface opt, Map<String, ILanguage> list) {
    this(list, opt.getFiles(), opt.getGenerate(), opt.getMerge());
  }

  public Main(Map<String, ILanguage> list, List<File> file, List<File> generate, List<File> merge) {
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
    if (!opt.isFilesSet()) {
      System.err.println("I need at least one input file!");
      System.err.println(BAD_USAGE_MSG);
      return;
    }    
    
    Map<String, ILanguage> list = new HashMap<String, ILanguage>();
    list.put("coq", new CoqLanguage());
    list.put("nat", new NaturalLanguage());
    list.put("gen", new GenericLanguage());
        
    Main main = new Main(opt, list);
    main.start();

  }

  public void start() {
    for (File in: fInput) {
      for (ILanguage lang: fLang.values()) {
        if(lang.isLanguageFile(in)) {
          lang.addInput(in);
        }
      }    
    }
    for (File gen: fGenerate) {
      for (ILanguage lang: fLang.values()) {
        if(lang.isLanguageFile(gen)) {
          lang.addGenerate(gen);
        }
      }    
    }
    for (File merge: fMerge) {
      for (ILanguage lang: fLang.values()) {
        if(lang.isLanguageFile(merge)) {
          lang.addMerge(merge);
        }
      }    
    }
    
    System.out.println("1: Preparation phase");
    for (ILanguage lang: fLang.values()) {
      lang.prepare();
    }
    
    System.out.println("2: Generation phase");
    for (ILanguage lang: fLang.values()) {
      lang.generate();
    }
  }

}
