/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon;

import static ie.ucd.clops.util.OptionUtil.SortingOption.ALPHABETICAL_BY_FIRST_ALIAS;
import ie.ucd.bon.clinterface.BONcOptionStore;
import ie.ucd.bon.clinterface.BONcOptionsInterface;
import ie.ucd.bon.clinterface.BONcParser;
import ie.ucd.bon.errorreporting.FileNotFoundError;
import ie.ucd.bon.errorreporting.NoFilesError;
import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.graph.display.PrefuseGraphDisplay;
import ie.ucd.bon.parser.tracker.ParseResult;
import ie.ucd.bon.parser.tracker.ParsingTracker;
import ie.ucd.bon.source.SourceReader;
import ie.ucd.bon.typechecker.TypingInformation;
import ie.ucd.bon.util.FileUtil;
import ie.ucd.clops.util.OptionUtil;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.antlr.runtime.RecognitionException;

/**
 * 
 * @author Fintan
 *
 */
public final class Main {

  public static final int TC_NUM_SEVERE_ERRORS = 2; //NB for all files
  public static final int PP_NUM_SEVERE_ERRORS = 0; //NB for one file
  public static final int CCG_NUM_SEVERE_ERRORS = 10; //NB for all files
  public static final int IG_NUM_SEVERE_ERRORS = 10; //NB for all files

  private static boolean debug = false;
  private static String version;

  private static Problems problems;  
  private static TypingInformation typingInfo;

  /** Prevent instantiation of Main. */
  private Main() { }

  public static boolean isDebug() {
    return debug;
  }

  public static void logDebug(final String debugMessage) {
    if (debug) {
      System.out.println("Debug: " + debugMessage);
    }
  }

  /**
   * Get the version of BONc that is running.
   * @return a string containing the version number of BONc.
   */
  public static String getVersion() {
    if (version == null) {
      try {
        version = FileUtil.readToString("version");
      } catch (IOException ioe) {
        version = "An error occurred when reading the version.";
      }
    }
    return version;
  }

  public static void main(final String[] args) {
    try {
      main2(args, true);
    } catch (Exception e) {
      System.out.println("Uncaught exception: " + e);
      e.printStackTrace(System.out);
    }
  }

  public static boolean main2(final String[] args, final boolean exitOnFailure) {
    try {
      //CLOLogger.setLogLevel(Level.FINE);
      BONcParser clParser = new BONcParser();

      if (clParser.parse(args)) {
        BONcOptionStore options = clParser.getOptionStore();

        debug = options.isDebugSet() && options.getDebug(); 

        if (options.getPrintMan()) {
          OptionUtil.printOptionsInManFormat(System.out, OptionUtil.sortOptions(options, ALPHABETICAL_BY_FIRST_ALIAS));
          return true;
        } else if (options.getPrintReadme()) {
          OptionUtil.printOptions(System.out, OptionUtil.sortOptions(options, ALPHABETICAL_BY_FIRST_ALIAS), 80, 2);
          return true;
        } else if (options.getPrintBashCompletion()) {
          OptionUtil.printBashCompletionOptionsScript(System.out, options.getOptionsWithoutErrorOption(), "bonc");
          return true;
        } else if (options.getHelp()) {
          System.out.println(getVersion());
          System.out.println("Options:");
          OptionUtil.printOptions(System.out, OptionUtil.sortOptions(options, ALPHABETICAL_BY_FIRST_ALIAS), 80, 2);
          return true;
        } else if (options.getVersion()) {
          System.out.println(getVersion());
          return true;
        } else {
          List<File> files = options.getSourceFiles();
          Main.logDebug(files.size() + " files:");
          for (File file : files) {
            Main.logDebug("\t" + file.getPath());
          }
          boolean success = run(files, options);
          if (!success && exitOnFailure) {
            System.exit(1);
          } else {
            return success;
          }
        }
      } 
      //TODO print usage  
      System.out.println("Invalid arguments.");
      return false;

    } catch (Exception e) {
      System.out.println("Something went wrong.");
      e.printStackTrace();
      if (exitOnFailure) {
        System.exit(1);
      }
      return false;
    }
  }

  private static List<File> getValidFiles(final List<File> fileNames, final ParsingTracker tracker, final BONcOptionsInterface so) {
    //Check valid files
    List<File> validFiles = new ArrayList<File>(fileNames.size());

    if (so.getReadFromStdin()) {
      Main.logDebug("Reading from stdin");
      validFiles.add(null);
    }

    //TODO clops now handles this.
    for (File file : fileNames) {
      if (file.exists() && !file.isDirectory()) {
        validFiles.add(file);
      } else {
        tracker.addProblem(new FileNotFoundError(file));
      }
    }
    return validFiles;
  }

  private static void parse(final Collection<File> files, final ParsingTracker tracker, final boolean timing) {

    for (File file : files) {
      ParseResult parseResult;

      InputStream is;
      if (file == null) {
        is = SourceReader.getInstance().readStandardInput();
      } else {
        try {
          is = SourceReader.getInstance().readFile(file);
        } catch (FileNotFoundException fnfe) {
          is = null;
        } catch (IOException ioe) {
          is = null;
        }
      }

      try {
        if (timing) {
          long startTime = System.nanoTime();
          parseResult = Parser.parse(file, is, tracker);
          long endTime = System.nanoTime();
          System.out.println("Parsing took: " + timeString(endTime - startTime));
        } else {
          parseResult = Parser.parse(file, is, tracker);
        }

        if (file == null) {
          tracker.addParse("stdin", parseResult);
        } else {
          tracker.addParse(file.getPath(), parseResult);
        }
      } catch (RecognitionException re) {
        //Nothing - won't actually happen?
        System.out.println("ERROR, something went wrong...");
      }
    }
  }

  private static void typeCheck(final ParsingTracker tracker, final BONcOptionsInterface so, final boolean timing) {
    boolean checkInformal = so.getCheckInformal();
    boolean checkFormal = so.getCheckFormal();
    boolean checkConsistency = so.getCheckConsistency();
    boolean typeCheck = so.getTypecheck();
    Main.logDebug("typeCheck: " + typeCheck + ", checkInformal: " + checkInformal + ", checkFormal: " + checkFormal + ", checkConsistency: " + checkConsistency);

    if (tracker.continueFromParse(TC_NUM_SEVERE_ERRORS)) {
      try {
        if (timing) {
          long startTime = System.nanoTime();
          TypeChecker.typeCheck(tracker, typeCheck, checkInformal, checkFormal, checkConsistency);
          long endTime = System.nanoTime();
          System.out.println("Typechecking took: " + timeString(endTime - startTime));
        } else {
          TypeChecker.typeCheck(tracker, typeCheck, checkInformal, checkFormal, checkConsistency);
        }

      } catch (RecognitionException re) {
        //Nothing - won't actually happen?
        System.out.println("ERROR, something went wrong...");
      }

    } else {
      tracker.setFinalMessage("Not typechecking due to parse errors.");
    }
  }

  private static void print(final Collection<File> files, final ParsingTracker tracker, final BONcOptionsInterface options, final boolean timing) {

    if (!options.isPrintSet()) {
      return;
    }

    BONcOptionsInterface.Print printType = options.getPrint();

    if (options.getGenClassDic() && printType != BONcOptionsInterface.Print.DIC) {
      try {
        String classDic = Printer.printGeneratedClassDictionaryToString(tracker);
        File classDicAutoFile = new File("class-dic-auto");
        if (!classDic.equals("")) {
          tracker.addParse(classDicAutoFile.getName(), Parser.parse(classDicAutoFile, new ByteArrayInputStream(classDic.getBytes()), tracker));
          files.add(classDicAutoFile);
        }
      } catch (RecognitionException re) {
        //Can't actually be thrown for this.
        logDebug("Main: Threw RecognitionException while executing printGeneratedClassDictionaryToString");
      }
    }

    boolean printToFile = options.isPrintOutputSet();

    PrintStream outputStream;
    File outputFile = null;
    if (printToFile) {
      outputFile = options.getPrintOutput();

      try {
        FileOutputStream outputFileStream = new FileOutputStream(outputFile);
        outputStream = new PrintStream(outputFileStream);

        Main.logDebug("printing: " + printType + ", to: " + outputFile.getPath());
      } catch (FileNotFoundException fnfe) {
        System.out.println("Error writing to file " + outputFile.getPath());
        return;
      }
    } else {
      outputStream = System.out;
      Main.logDebug("printing: " + printType + ", to: stdout");
    }  


    Printer.printToStream(files, tracker, outputStream, printType, printToFile, timing);

    if (printToFile) {
      outputStream.close();
      System.out.println("Succesfully created: " + outputFile.getPath());
    }
  }

  public static boolean run(final List<File> fileNames, final BONcOptionsInterface so) {
    problems = null;
    //Timing info?
    boolean timing = so.getTime();

    ParsingTracker tracker = new ParsingTracker();
    List<File> validFiles = getValidFiles(fileNames, tracker, so);

    //Is there at least one valid file?
    if (validFiles.size() < 1) {
      tracker.addProblem(new NoFilesError());
      printResults(tracker, false, false, false);
      return false;
    }

    parse(validFiles, tracker, timing);
    typeCheck(tracker, so, timing);

    boolean checkInformal = so.getCheckInformal();
    boolean checkFormal = so.getCheckFormal();
    boolean checkConsistency = so.getCheckConsistency();
    printResults(tracker, checkInformal, checkFormal, checkConsistency);    

    print(validFiles, tracker, so, timing);
    //graph(tracker, so);
    displayGraphs(tracker, so);

    //TODO - return false here if we have problems...
    return tracker.getErrorsAndWarnings(checkInformal, checkFormal, checkConsistency).getNumberOfErrors() == 0;
  }

  private static void printResults(final ParsingTracker tracker, final boolean checkInformal, final boolean checkFormal, final boolean checkConsistency) {
    problems = tracker.getErrorsAndWarnings(checkInformal, checkFormal, checkConsistency);
    typingInfo = tracker.getTypingInformation();
    problems.printProblems(System.out);
    problems.printSummary(System.out);
    tracker.printFinalMessage(System.out);
  }

  private static void displayGraphs(final ParsingTracker tracker, final BONcOptionsInterface so) {
    if (so.isGraphSet()) {
      System.out.println("Graphing...");
      PrefuseGraphDisplay.displayGraph(so.getGraph(), tracker);
    }
  }

  public static String timeString(final long timeInNano) {
    return timeInNano + "ns (" + (timeInNano / 1000000d) + "ms or " + (timeInNano / 1000000000d) + "s)";
  }

  public static Problems getProblems() {
    return problems;
  }

  public static TypingInformation getTypingInfo() {
    if (typingInfo != null) {
      typingInfo.finalProcess();
    }
    return typingInfo;
  }

}
