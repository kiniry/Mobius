/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon;

import ie.ucd.bon.Printer.PrintingOption;
import ie.ucd.bon.errorreporting.FileNotFoundError;
import ie.ucd.bon.errorreporting.NoFilesError;
import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.parser.tracker.ParseResult;
import ie.ucd.bon.parser.tracker.ParsingTracker;
import ie.ucd.commandline.actions.TriggersBoolean;
import ie.ucd.commandline.constraints.MutuallyExclusiveConstraint;
import ie.ucd.commandline.constraints.RequiresConstraint;
import ie.ucd.commandline.options.BooleanDefaultOption;
import ie.ucd.commandline.options.InvalidOptionsSetException;
import ie.ucd.commandline.options.Options;
import ie.ucd.commandline.options.StringDefaultOption;
import ie.ucd.commandline.parser.CommandlineParser;
import ie.ucd.commandline.parser.CommandlineParser.SortingOption;

import java.io.File;
import java.util.Collection;
import java.util.Vector;

import org.antlr.runtime.RecognitionException;

/**
 * 
 * @author Fintan
 *
 */
public class Main {

  private static final int TC_NUM_SEVERE_ERRORS = 2; //NB for all files
  private static final int PP_NUM_SEVERE_ERRORS = 1; //NB for one file
  private static final int CCG_NUM_SEVERE_ERRORS = 10; //NB for all files
  private static final int IG_NUM_SEVERE_ERRORS = 10; //NB for all files
  
  private static boolean debug = false;
  
  public static boolean isDebug() {
    return debug;
  }
  
  public static void logDebug(final String debugMessage) {
    if (debug) {
      System.out.println("Debug: " + debugMessage);
    }
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
        } else if (so.isBooleanOptionByNameSelected("-hh")) {
          cp.printOptions(System.out, true);
        } else if (so.isBooleanOptionByNameSelected("--help")) {
          cp.printOptions(System.out, false);
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
      try {
        if (timing) {
          long startTime = System.nanoTime();
          parseResult = Parser.parse(file, tracker);
          long endTime = System.nanoTime();
          System.out.println("Parsing took: " + timeString(endTime-startTime));
        } else {
          parseResult = Parser.parse(file, tracker);
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

    if(so.isStringOptionByNameSelected("-pp")) {
      if (so.isStringOptionByNameSelected("-ppo")) {
        String outputDirPath = so.getStringOptionByNameArgument("-ppo");
        File outputDirectory = new File(outputDirPath);

        String printTypes = so.getStringOptionByNameArgument("-pp");
        Collection<PrintingOption> printingOptions = Printer.getPrintingOptionsList(printTypes, ";");

        for (PrintingOption po : printingOptions) {
          
          for (File file : files) {
            String fileName;
            if (file == null) {
              fileName = "stdin";
            } else {
              fileName = file.getPath();
            }
            ParseResult parse = tracker.getParseResult(fileName);
            if (parse.continueFromParse(PP_NUM_SEVERE_ERRORS)) {
              try {
                if (timing) {
                  long startTime = System.nanoTime();
                  Printer.printToFile(parse, outputDirectory, po);
                  long endTime = System.nanoTime();
                  System.out.println("Printing " + Printer.getPrintingOptionName(po) + " took: " + timeString(endTime-startTime));
                } else {
                  Printer.printToFile(parse, outputDirectory, po);
                }
              } catch (RecognitionException re) {
                System.out.println("Something went wrong when printing...");
              }
              
            } else {
              System.out.println("Not printing " + fileName + " due to parse errors.");
            }
          }
        }
      } else {
        System.out.println("Pretty printing to System.out:");
        for (File file : files) {
          String fileName;
          if (file == null) {
            fileName = "stdin";
          } else {
            fileName = file.getPath();
          }
          ParseResult parse = tracker.getParseResult(fileName);
          if (parse.continueFromParse(PP_NUM_SEVERE_ERRORS)) {
            try {
              if (timing) {
                long startTime = System.nanoTime();
                Printer.prettyPrintToStream(parse, System.out);
                long endTime = System.nanoTime();
                System.out.println("Pretty-printing to System.out took: " + timeString(endTime-startTime));
              } else {
                Printer.prettyPrintToStream(parse, System.out);
              }
            } catch (RecognitionException re) {
              System.out.println("Something went wrong when printing...");
            }
          } else {
            System.out.println("Not printing " + fileName + " due to parse errors.");
          }
        }
      }
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
    CommandlineParser cp = new CommandlineParser("bonc", SortingOption.ALPHABETICAL_OPTION, 1);
    cp.setStartHelpString("BON Parser and Typechecker.");
    cp.setDefaultUsageString("bonc [options] file1 [file2 ...]");

    BooleanDefaultOption tc = new BooleanDefaultOption();
    tc.setOptionID("1");
    tc.addOptionName("-tc");
    tc.addOptionName("--typecheck");
    tc.setHelpString("Typecheck the input.");
    tc.setByDefault();
    tc.setHidden();
    cp.addOption(tc);
    
    BooleanDefaultOption ntc = new BooleanDefaultOption();
    ntc.setOptionID("1.1");
    ntc.addOptionName("-ntc");
    ntc.addOptionName("--no-typecheck");
    ntc.setHelpString("Do not typecheck the input.");
    ntc.addAction(new TriggersBoolean("1.1", "1", false));
    cp.addOption(ntc);    
    
    StringDefaultOption pp = new StringDefaultOption();
    pp.setOptionID("2");
    pp.addOptionName("-pp");
    pp.addOptionName("--pretty-print");
    pp.setHelpString("Pretty-print the parsed input");
    cp.addOption(pp);
    
    StringDefaultOption ppo = new StringDefaultOption();
    ppo.setOptionID("2.1");
    ppo.addOptionName("-ppo");
    ppo.addOptionName("--pretty-print-output");
    ppo.setHelpString("Output directory for printed output.");
    ppo.addConstraint(new RequiresConstraint("2.1", "2"));
    cp.addOption(ppo);
    
    BooleanDefaultOption help = new BooleanDefaultOption();
    help.setOptionID("3");
    help.addOptionName("-h");
    help.addOptionName("--help");
    help.setHelpString("Print this help message");
    cp.addOption(help);
    
    BooleanDefaultOption hiddenhelp = new BooleanDefaultOption();
    hiddenhelp.setOptionID("3.1");
    hiddenhelp.addOptionName("-hh");
    hiddenhelp.addOptionName("--hidden-help");
    hiddenhelp.setHelpString("Print help with hidden options shown");
    hiddenhelp.setHidden();
    cp.addOption(hiddenhelp);
    
    BooleanDefaultOption time = new BooleanDefaultOption();
    time.setOptionID("4");
    time.addOptionName("-t");
    time.addOptionName("-time");
    time.addOptionName("--time");
    time.setHelpString("Print timing information.");
    cp.addOption(time);
    
    StringDefaultOption cg = new StringDefaultOption();
    cg.setOptionID("5");
    cg.addOptionName("-cg");
    cg.setHelpString("Print class and cluster graph in the .dot file format.");
    cg.setHidden(); //Hidden until revisiting
    cp.addOption(cg);
    
    StringDefaultOption ig = new StringDefaultOption();
    ig.setOptionID("6");
    ig.addOptionName("-ig");
    ig.setHelpString("Print class inheritence graph in the .dot file format.");
    ig.setHidden(); //Hidden until revisiting
    cp.addOption(ig);
    
    BooleanDefaultOption informal = new BooleanDefaultOption();
    informal.setOptionID("10.0");
    informal.addOptionName("-i");
    informal.addOptionName("-informal");
    informal.addOptionName("--informal");
    informal.setHelpString("Only check informal charts.");
    informal.addAction(new TriggersBoolean("10.0", "10.6", false)); //Informal means no formal
    informal.addAction(new TriggersBoolean("10.0", "11", false)); //Informal also means no consistency checking
    cp.addOption(informal);
    
    BooleanDefaultOption formal = new BooleanDefaultOption();
    formal.setOptionID("10.5");
    formal.addOptionName("-f");
    formal.addOptionName("-formal");
    formal.addOptionName("--formal");
    formal.setHelpString("Only check formal charts.");
    //formal.setByDefault();
    formal.addAction(new TriggersBoolean("10.5", "10.1", false)); //formal means no informal
    formal.addAction(new TriggersBoolean("10.5", "11", false)); //Informal also means no consistency checking
    
    formal.addConstraint(new MutuallyExclusiveConstraint("10.5", "10.0"));
    cp.addOption(formal);
    
    BooleanDefaultOption checkInformal = new BooleanDefaultOption();
    checkInformal.setOptionID("10.1");
    checkInformal.addOptionName("-ci");
    checkInformal.addOptionName("--check-informal");
    checkInformal.setHelpString("Check informal charts.");
    checkInformal.setByDefault();
    checkInformal.setHidden();
    cp.addOption(checkInformal);
    
    BooleanDefaultOption checkFormal = new BooleanDefaultOption();
    checkFormal.setOptionID("10.6");
    checkFormal.addOptionName("-cf");
    checkFormal.addOptionName("--check-formal");
    checkFormal.setHelpString("Check formal diagrams.");
    checkFormal.setByDefault();
    checkFormal.setHidden();
    cp.addOption(checkFormal);
    
    BooleanDefaultOption consistency = new BooleanDefaultOption();
    consistency.setOptionID("11");
    consistency.addOptionName("-cc");
    consistency.addOptionName("--check-consistency");
    consistency.setHelpString("Check consistency between levels.");
    consistency.setByDefault();
    consistency.setHidden();
    cp.addOption(consistency);
    
    BooleanDefaultOption noConsistency = new BooleanDefaultOption();
    noConsistency.setOptionID("11.1");
    noConsistency.addOptionName("-nc");
    noConsistency.addOptionName("--no-consistency");
    noConsistency.setHelpString("Do not check consistency between levels.");
    noConsistency.addAction(new TriggersBoolean("11.1", "11", false));
    //noConsistency.addConstraint(new MutuallyExclusiveConstraint("11", "11.1"));
    cp.addOption(noConsistency);
    
    BooleanDefaultOption debug = new BooleanDefaultOption();
    debug.setOptionID("99");
    debug.addOptionName("-d");
    debug.addOptionName("--debug");
    debug.setHelpString("Print debugging output.");
    cp.addOption(debug);
    
    BooleanDefaultOption stdin = new BooleanDefaultOption();
    stdin.setOptionID("9");
    stdin.addOptionName("-");
    stdin.setHelpString("Read from standard input.");    
    cp.addOption(stdin);
    
    BooleanDefaultOption printMan = new BooleanDefaultOption();
    printMan.setOptionID("99999");
    printMan.setHidden();
    printMan.addOptionName("-pm");
    printMan.addOptionName("--print-man");
    printMan.setHelpString("Print available options in man-page format");
    cp.addOption(printMan);
    
    cp.parseOptions(System.out, args);
    cp.checkConstraints(System.out);
    cp.triggerActions();

    return cp;
  }
  
  private static String timeString(long timeInNano) {
    return timeInNano + "ns (" + (timeInNano / 1000000d) + "ms or " + (timeInNano / 1000000000d) + "s)";
  }
  
  public static Problems getProblems() {
    return problems;
  }

}
