/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon;

import ie.ucd.bon.Printer.PrintingOption;
import ie.ucd.bon.errorreporting.FileNotFoundError;
import ie.ucd.bon.errorreporting.NoFilesError;
import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.parser.SourceReader;
import ie.ucd.bon.parser.tracker.ParseResult;
import ie.ucd.bon.parser.tracker.ParsingTracker;
import ie.ucd.bon.util.FileUtil;
import ie.ucd.commandline.options.InvalidOptionsSetException;
import ie.ucd.commandline.options.Options;
import ie.ucd.commandline.parser.CommandlineParser;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.util.Collection;
import java.util.Vector;

import org.antlr.runtime.RecognitionException;

/**
 * 
 * @author Fintan
 *
 */
public class Main {

  public static final int TC_NUM_SEVERE_ERRORS = 2; //NB for all files
  public static final int PP_NUM_SEVERE_ERRORS = 0; //NB for one file
  public static final int CCG_NUM_SEVERE_ERRORS = 10; //NB for all files
  public static final int IG_NUM_SEVERE_ERRORS = 10; //NB for all files
  
  private static boolean debug = false;
  
  public static boolean isDebug() {
    return debug;
  }
  
  public static void logDebug(final String debugMessage) {
    if (debug) {
      System.out.println("Debug: " + debugMessage);
    }
  }
  
  private static String version;
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
  
  private static Problems problems; 
  
  public static void main(final String[] args) {
    try {
      main2(args, true);
    } catch (Exception e) {
      System.out.println("Uncaught exception: " + e);
      e.printStackTrace(System.out);
    }
  }
  
  public static void main2(final String[] args, final boolean exitOnFailure) {
    try {
      CommandlineParser cp = processArguments(args);
      
      if (cp.isValidParse()) {
        Options so = cp.getSelectedOptions();
        
        debug = so.isBooleanOptionByNameSelected("-d");
        
        if (so.isBooleanOptionByNameSelected("--print-man")) {
          cp.printOptionsInManFormat(System.out, CommandlineParser.SortingOption.ALPHABETICAL_OPTION, false);
        } else if (so.isBooleanOptionByNameSelected("--print-readme")) {
          cp.printOptionsInReadmeFormat(System.out, CommandlineParser.SortingOption.ALPHABETICAL_OPTION, false, 80, 2);
        } else if (so.isBooleanOptionByNameSelected("--print-bash-completion")) {
          cp.printBashCompletionOptionsScript(System.out, false);
        } else if (so.isBooleanOptionByNameSelected("-hh")) {
          cp.printOptions(System.out, true);
        } else if (so.isBooleanOptionByNameSelected("--help")) {
          cp.printOptions(System.out, false);
        } else if (so.isBooleanOptionByNameSelected("--version")) {
          System.out.println(getVersion());
        } else {
          Collection<String> files = cp.getActualArgs();
          Main.logDebug(files.size() + " files:");
          for (String file : files) {
            Main.logDebug("\t" + file);
          }
          boolean success = run(cp.getActualArgs(), so);
          if (!success && exitOnFailure) {
            System.exit(1);
          }
        }
      }
    } catch (InvalidOptionsSetException iose) {
      //This shouldn't happen, if the options are set up correctly!
      //System.out.println("Error: ");
      System.exit(1);
    } 
  }
  
  private static Collection<File> getValidFiles(Collection<String> fileNames, ParsingTracker tracker, Options so) {
    //Check valid files
    Collection<File> validFiles = new Vector<File>();
    
    boolean readingFromStdIn = false;
    if (so.isBooleanOptionByNameSelected("-")) {
      Main.logDebug("Reading from stdin");
      validFiles.add(null);
      readingFromStdIn = true;
    }
    
    for (String fileName : fileNames) {
      if ("-".equals(fileName)) {
        if (!readingFromStdIn) {
          Main.logDebug("Reading from stdin");
          validFiles.add(null);
          readingFromStdIn = true;
        }
        continue;
      }
      File file = new File(fileName);
      if (file.exists() && !file.isDirectory()) {
        validFiles.add(file);
      } else {
        tracker.addProblem(new FileNotFoundError(file));
      }
    }
    return validFiles;
  }
  
  private static void parse(Collection<File> files, ParsingTracker tracker, boolean timing) {
 
    for (File file : files) {
      ParseResult parseResult;
      
      InputStream is;
      if (file == null) {
        is = SourceReader.getInstance().readStandardInput();
      } else {
        try {
          //is = new FileInputStream(file);
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
          System.out.println("Parsing took: " + timeString(endTime-startTime));
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
  
  private static void typeCheck(ParsingTracker tracker, Options so, boolean timing) {
    if (so.isBooleanOptionByNameSelected("-tc")) {

      boolean checkInformal = so.isBooleanOptionByNameSelected("-ci");
      boolean checkFormal = so.isBooleanOptionByNameSelected("-cf");
      boolean checkConsistency = so.isBooleanOptionByNameSelected("-cc");
      Main.logDebug("checkInformal: " + checkInformal + ", checkFormal: " + checkFormal + ", checkConsistency: " + checkConsistency);
      
      if (tracker.continueFromParse(TC_NUM_SEVERE_ERRORS)) {
        try {
          if (timing) {
            long startTime = System.nanoTime();
            TypeChecker.typeCheck(tracker, checkInformal, checkFormal, checkConsistency);
            long endTime = System.nanoTime();
            System.out.println("Typechecking took: " + timeString(endTime-startTime));
          } else {
            TypeChecker.typeCheck(tracker, checkInformal, checkFormal, checkConsistency);
          }

        } catch (RecognitionException re) {
          //Nothing - won't actually happen?
          System.out.println("ERROR, something went wrong...");
        }
        
      } else {
        tracker.setFinalMessage("Not typechecking due to parse errors.");
      }
    } else {
      System.out.println("Not typechecking.");
    }
  }
  
  private static void print(Collection<File> files, ParsingTracker tracker, Options so, boolean timing) {

    if(!so.isStringOptionByNameSelected("-p")) {
      return;
    }

    String printType = so.getStringOptionByNameArgument("-p");
    PrintingOption printingOption = Printer.getPrintingOption(printType);
    if (printingOption == Printer.PrintingOption.NONE) {
      System.out.println("Unknown print type \"" + printType + "\"");
      return;
    }
    
    if (so.isBooleanOptionByNameSelected("-gcd") && printingOption != Printer.PrintingOption.DIC) {
      try {
        String classDic = Printer.printGeneratedClassDictionaryToString(tracker);
        File classDicAutoFile = new File("class-dic-auto");
        if (!classDic.equals("")) {
          tracker.addParse(classDicAutoFile.getName(), Parser.parse(classDicAutoFile, new ByteArrayInputStream(classDic.getBytes()), tracker));
          files.add(classDicAutoFile);
        }
      } catch (RecognitionException re) {
        //Can't actually be thrown for this.
      }
    }
    
    boolean printToFile = so.isStringOptionByNameSelected("-po");
    
    PrintStream outputStream;
    String outputFilePath = null;
    if (printToFile) {
      outputFilePath = so.getStringOptionByNameArgument("-po");
      File outputFile = new File(outputFilePath);
      
      try {
        FileOutputStream outputFileStream = new FileOutputStream(outputFile);
        outputStream = new PrintStream(outputFileStream);
        
        Main.logDebug("printing: " + printType + ", to: " + outputFilePath);
      } catch (FileNotFoundException fnfe) {
        System.out.println("Error writing to file " + outputFilePath);
        return;
      }
    } else {
      outputStream = System.out;
      Main.logDebug("printing: " + printType + ", to: stdout");
    }  


    Printer.printToStream(files, tracker, outputStream, printingOption, printToFile, timing);
    
    if (printToFile) {
      outputStream.close();
      System.out.println("Succesfully created: " + outputFilePath);
    }
  }
  
  private static void graph(ParsingTracker tracker, Options so) {
    //Class and Cluster graph
    if (so.isStringOptionByNameSelected("-cg")) {
      if (tracker.continueFromParse(CCG_NUM_SEVERE_ERRORS)) {
        System.out.println("Not creating class-cluster graph due to parse errors.");
      } else {
        System.out.println("Creating class-cluster graph: " + so.getStringOptionByNameArgument("-cg"));
        Grapher.graphClassesAndClusters(tracker, so.getStringOptionByNameArgument("-cg"));
      }
    }
    //Class inheritence graph
    if (so.isStringOptionByNameSelected("-ig")) {
      if (tracker.continueFromParse(IG_NUM_SEVERE_ERRORS)) {
        System.out.println("Not creating inheritence graph due to parse errors.");
      } else {
        System.out.println("Creating class-inheritence graph: " + so.getStringOptionByNameArgument("-ig"));
        Grapher.graphClassHierarchy(tracker, so.getStringOptionByNameArgument("-ig"));
      }
    }
  }
  
  public static boolean run(Collection<String> fileNames, Options so) {
    //Timing info?
    boolean timing = so.isBooleanOptionByNameSelected("-time");
    
    ParsingTracker tracker = new ParsingTracker();
    Collection<File> validFiles = getValidFiles(fileNames, tracker, so);
    
    //Is there at least one valid file?
    if (validFiles.size() < 1) {
      tracker.addProblem(new NoFilesError());
      printResults(tracker, false, false, false);
      return false;
    }
    
    parse(validFiles, tracker, timing);
    typeCheck(tracker, so, timing);
    
    boolean checkInformal = so.isBooleanOptionByNameSelected("-ci");
    boolean checkFormal = so.isBooleanOptionByNameSelected("-cf");
    boolean checkConsistency = so.isBooleanOptionByNameSelected("-cc");
    printResults(tracker, checkInformal, checkFormal, checkConsistency);    
    
    print(validFiles, tracker, so, timing);
    graph(tracker, so);

    //TODO - return false here if we have problems...
    return true;
  }
  
  private static void printResults(ParsingTracker tracker, boolean checkInformal, boolean checkFormal, boolean checkConsistency) {
    problems = tracker.getErrorsAndWarnings(checkInformal, checkFormal, checkConsistency);
    problems.printProblems(System.out);
    problems.printSummary(System.out);
    tracker.printFinalMessage(System.out);
  }

  private static CommandlineParser processArguments(String[] args) throws InvalidOptionsSetException {
    CommandlineParser clp = CLP.commandlineParser();
    
    clp.parseOptions(System.out, args);
    clp.checkConstraints(System.out);
    clp.triggerActions();

    return clp;
  }
  
  public static String timeString(long timeInNano) {
    return timeInNano + "ns (" + (timeInNano / 1000000d) + "ms or " + (timeInNano / 1000000000d) + "s)";
  }
  
  public static Problems getProblems() {
    return problems;
  }

}
