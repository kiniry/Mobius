package ie.ucd.bon.clinterface;

import ie.ucd.clops.runtime.options.CLOPSErrorOption;
import ie.ucd.clops.runtime.options.OptionGroup;
import ie.ucd.clops.runtime.options.OptionStore;
import ie.ucd.clops.runtime.options.exception.InvalidOptionPropertyValueException;
import java.util.List;
import java.io.File;
import ie.ucd.clops.runtime.options.EnumOption;
import ie.ucd.clops.runtime.options.BooleanOption;
import ie.ucd.clops.runtime.options.FileOption;
import ie.ucd.clops.runtime.options.FileListOption;

public class BONcOptionStore extends OptionStore implements BONcOptionsInterface {

  private final EnumOption ogPrint;
  private final FileOption ogPrintOutput;
  private final BooleanOption ogPrettyPrint;
  private final BooleanOption ogPrintMan;
  private final BooleanOption ogPrintReadme;
  private final BooleanOption ogPrintBashCompletion;
  private final BooleanOption ogHelp;
  private final BooleanOption ogTime;
  private final BooleanOption ogTypecheck;
  private final BooleanOption ogInformal;
  private final BooleanOption ogFormal;
  private final BooleanOption ogCheckInformal;
  private final BooleanOption ogCheckFormal;
  private final BooleanOption ogCheckConsistency;
  private final BooleanOption ogDebug;
  private final BooleanOption ogReadFromStdin;
  private final BooleanOption ogGenClassDic;
  private final EnumOption ogGraph;
  private final BooleanOption ogVersion;
  private final FileListOption ogSourceFiles;
  private final CLOPSErrorOption CLOPSERROROPTION;

  public BONcOptionStore() throws InvalidOptionPropertyValueException {

    //Options
    ogPrint = new EnumOption("Print", "(?:-p)|(?:--print)");
    addOption(ogPrint);
    ogPrint.setProperty("choices", "SYSO,TXT,DOT,HTML,DIC,IIG,ICG,CL,PICG,PIIG");
    ogPrint.setProperty("casesensitive", "false");
    ogPrint.setProperty("aliases", "-p,--print");
    ogPrint.setProperty("description", "Print the parsed input in the given format. TXT for plain-text, HTML for html generation of informal charts, DIC to generate the class dictionary, IIG for the informal class inheritance graph. See the manpage or README.txt for more information and a list of all printing options.");
    ogPrintOutput = new FileOption("PrintOutput", "(?:-po)|(?:--print-output)");
    addOption(ogPrintOutput);
    ogPrintOutput.setProperty("canbedir", "false");
    ogPrintOutput.setProperty("aliases", "-po,--print-output");
    ogPrintOutput.setProperty("description", "Print output to the given file instead of to stdout.");
    ogPrettyPrint = new BooleanOption("PrettyPrint", "(?:-pp)|(?:--pretty-print)");
    addOption(ogPrettyPrint);
    ogPrettyPrint.setProperty("aliases", "-pp,--pretty-print");
    ogPrettyPrint.setProperty("description", "Pretty-print the parsed input. This is equivalent to -p=TXT.");
    ogPrintMan = new BooleanOption("PrintMan", "(?:--print-man)");
    addOption(ogPrintMan);
    ogPrintMan.setProperty("default", "false");
    ogPrintMan.setProperty("aliases", "--print-man");
    ogPrintMan.setProperty("description", "Print available options in man-page format.");
    ogPrintReadme = new BooleanOption("PrintReadme", "(?:--print-readme)");
    addOption(ogPrintReadme);
    ogPrintReadme.setProperty("default", "false");
    ogPrintReadme.setProperty("aliases", "--print-readme");
    ogPrintReadme.setProperty("description", "Print available options in readme format.");
    ogPrintBashCompletion = new BooleanOption("PrintBashCompletion", "(?:--print-bash-completion)");
    addOption(ogPrintBashCompletion);
    ogPrintBashCompletion.setProperty("default", "false");
    ogPrintBashCompletion.setProperty("aliases", "--print-bash-completion");
    ogPrintBashCompletion.setProperty("description", "Print bash completion script for available options.");
    ogHelp = new BooleanOption("Help", "(?:-h)|(?:--help)");
    addOption(ogHelp);
    ogHelp.setProperty("default", "false");
    ogHelp.setProperty("aliases", "-h,--help");
    ogHelp.setProperty("description", "Print this help message.");
    ogTime = new BooleanOption("Time", "(?:-t)|(?:--time)");
    addOption(ogTime);
    ogTime.setProperty("default", "false");
    ogTime.setProperty("aliases", "-t,--time");
    ogTime.setProperty("description", "Print timing information.");
    ogTypecheck = new BooleanOption("Typecheck", "(?:-tc)|(?:--typecheck)");
    addOption(ogTypecheck);
    ogTypecheck.setProperty("default", "true");
    ogTypecheck.setProperty("aliases", "-tc,--typecheck");
    ogTypecheck.setProperty("description", "Typecheck the input");
    ogInformal = new BooleanOption("Informal", "(?:-i)|(?:--informal)");
    addOption(ogInformal);
    ogInformal.setProperty("aliases", "-i,--informal");
    ogInformal.setProperty("description", "Only check informal charts.");
    ogFormal = new BooleanOption("Formal", "(?:-f)|(?:--formal)");
    addOption(ogFormal);
    ogFormal.setProperty("aliases", "-f,--formal");
    ogFormal.setProperty("description", "Only check formal charts.");
    ogCheckInformal = new BooleanOption("CheckInformal", "(?:-ci)|(?:--check-informal)");
    addOption(ogCheckInformal);
    ogCheckInformal.setProperty("default", "true");
    ogCheckInformal.setProperty("aliases", "-ci,--check-informal");
    ogCheckInformal.setProperty("description", "Check informal charts.");
    ogCheckFormal = new BooleanOption("CheckFormal", "(?:-cf)|(?:--check-formal)");
    addOption(ogCheckFormal);
    ogCheckFormal.setProperty("default", "true");
    ogCheckFormal.setProperty("aliases", "-cf,--check-formal");
    ogCheckFormal.setProperty("description", "Check formal diagrams.");
    ogCheckConsistency = new BooleanOption("CheckConsistency", "(?:-cc)|(?:--check-consistency)");
    addOption(ogCheckConsistency);
    ogCheckConsistency.setProperty("default", "true");
    ogCheckConsistency.setProperty("aliases", "-cc,--check-consistency");
    ogCheckConsistency.setProperty("description", "Check consistency between levels.");
    ogDebug = new BooleanOption("Debug", "(?:-d)|(?:--debug)");
    addOption(ogDebug);
    ogDebug.setProperty("default", "false");
    ogDebug.setProperty("aliases", "-d,--debug");
    ogDebug.setProperty("description", "Print debugging output.");
    ogReadFromStdin = new BooleanOption("ReadFromStdin", "(?:-)");
    addOption(ogReadFromStdin);
    ogReadFromStdin.setProperty("default", "false");
    ogReadFromStdin.setProperty("aliases", "-");
    ogReadFromStdin.setProperty("description", "Read input from stdin.");
    ogGenClassDic = new BooleanOption("GenClassDic", "(?:-gcd)|(?:--gen-class-dic)");
    addOption(ogGenClassDic);
    ogGenClassDic.setProperty("default", "false");
    ogGenClassDic.setProperty("aliases", "-gcd,--gen-class-dic");
    ogGenClassDic.setProperty("description", "Generate the class dictionary when printing.");
    ogGraph = new EnumOption("Graph", "(?:-g)|(?:--graph)");
    addOption(ogGraph);
    ogGraph.setProperty("choices", "ICG,IIG");
    ogGraph.setProperty("casesensitive", "false");
    ogGraph.setProperty("aliases", "-g,--graph");
    ogGraph.setProperty("description", "Display the chosen graph type. ICG for informal clustering graph, IIG for informal inheritance graph.");
    ogVersion = new BooleanOption("Version", "(?:-v)|(?:-version)|(?:--version)");
    addOption(ogVersion);
    ogVersion.setProperty("default", "false");
    ogVersion.setProperty("aliases", "-v,-version,--version");
    ogVersion.setProperty("description", "Print BONc version and exit.");
    ogSourceFiles = new FileListOption("SourceFiles", "");
    addOption(ogSourceFiles);
    ogSourceFiles.setProperty("between", "");
    ogSourceFiles.setProperty("canbedir", "false");
    ogSourceFiles.setProperty("mustexist", "true");
    ogSourceFiles.setProperty("description", "Source files to process.");
  
    CLOPSERROROPTION = new ie.ucd.clops.runtime.options.CLOPSErrorOption();
    addOption(CLOPSERROROPTION);
  
    //Option groups
    final OptionGroup ogOption = new OptionGroup("Option");
    addOptionGroup(ogOption);
    final OptionGroup ogAloneOption = new OptionGroup("AloneOption");
    addOptionGroup(ogAloneOption);
    final OptionGroup ogAllOptions = new OptionGroup("AllOptions");
    addOptionGroup(ogAllOptions);
    
    //Setup groupings
    ogOption.addOptionOrGroup(ogCheckFormal);
    ogOption.addOptionOrGroup(ogCheckConsistency);
    ogOption.addOptionOrGroup(ogPrettyPrint);
    ogOption.addOptionOrGroup(ogReadFromStdin);
    ogOption.addOptionOrGroup(ogDebug);
    ogOption.addOptionOrGroup(ogPrint);
    ogOption.addOptionOrGroup(ogPrintOutput);
    ogOption.addOptionOrGroup(ogTime);
    ogOption.addOptionOrGroup(ogInformal);
    ogOption.addOptionOrGroup(ogGenClassDic);
    ogOption.addOptionOrGroup(ogGraph);
    ogOption.addOptionOrGroup(ogTypecheck);
    ogOption.addOptionOrGroup(ogCheckInformal);
    ogOption.addOptionOrGroup(ogFormal);
    ogAloneOption.addOptionOrGroup(ogHelp);
    ogAloneOption.addOptionOrGroup(ogPrintMan);
    ogAloneOption.addOptionOrGroup(ogVersion);
    ogAloneOption.addOptionOrGroup(ogPrintReadme);
    ogAloneOption.addOptionOrGroup(ogPrintBashCompletion);
    //AllOptions group
    ogAllOptions.addOptionOrGroup(ogPrint);
    ogAllOptions.addOptionOrGroup(ogPrintOutput);
    ogAllOptions.addOptionOrGroup(ogPrettyPrint);
    ogAllOptions.addOptionOrGroup(ogPrintMan);
    ogAllOptions.addOptionOrGroup(ogPrintReadme);
    ogAllOptions.addOptionOrGroup(ogPrintBashCompletion);
    ogAllOptions.addOptionOrGroup(ogHelp);
    ogAllOptions.addOptionOrGroup(ogTime);
    ogAllOptions.addOptionOrGroup(ogTypecheck);
    ogAllOptions.addOptionOrGroup(ogInformal);
    ogAllOptions.addOptionOrGroup(ogFormal);
    ogAllOptions.addOptionOrGroup(ogCheckInformal);
    ogAllOptions.addOptionOrGroup(ogCheckFormal);
    ogAllOptions.addOptionOrGroup(ogCheckConsistency);
    ogAllOptions.addOptionOrGroup(ogDebug);
    ogAllOptions.addOptionOrGroup(ogReadFromStdin);
    ogAllOptions.addOptionOrGroup(ogGenClassDic);
    ogAllOptions.addOptionOrGroup(ogGraph);
    ogAllOptions.addOptionOrGroup(ogVersion);
    ogAllOptions.addOptionOrGroup(ogSourceFiles);
  }
  
// Option Print.
// Aliases: [-p, --print]
  
  /**
   * {@inheritDoc}
   */
  public boolean isPrintSet() {
    return ogPrint.hasValue();
  }
  

  /** {@inheritDoc} */
  public Print getPrint() {
    return Print.get(ogPrint.getValue());
  }

  /** {@inheritDoc} */
  public String getRawPrint() {
    return ogPrint.getRawValue();
  }
  
  public EnumOption getPrintOption() {
    return ogPrint;
  }
  
// Option PrintOutput.
// Aliases: [-po, --print-output]
  
  /**
   * {@inheritDoc}
   */
  public boolean isPrintOutputSet() {
    return ogPrintOutput.hasValue();
  }
  
  /** {@inheritDoc} */
  public File getPrintOutput() {
    return ogPrintOutput.getValue();
  }

  /** {@inheritDoc} */
  public File getRawPrintOutput() {
    return ogPrintOutput.getRawValue();
  }
  
  public FileOption getPrintOutputOption() {
    return ogPrintOutput;
  }
  
// Option PrettyPrint.
// Aliases: [-pp, --pretty-print]
  
  /**
   * {@inheritDoc}
   */
  public boolean isPrettyPrintSet() {
    return ogPrettyPrint.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getPrettyPrint() {
    return ogPrettyPrint.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawPrettyPrint() {
    return ogPrettyPrint.getRawValue();
  }
  
  public BooleanOption getPrettyPrintOption() {
    return ogPrettyPrint;
  }
  
// Option PrintMan.
// Aliases: [--print-man]
  
  /**
   * {@inheritDoc}
   */
  public boolean isPrintManSet() {
    return ogPrintMan.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getPrintMan() {
    return ogPrintMan.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawPrintMan() {
    return ogPrintMan.getRawValue();
  }
  
  public BooleanOption getPrintManOption() {
    return ogPrintMan;
  }
  
// Option PrintReadme.
// Aliases: [--print-readme]
  
  /**
   * {@inheritDoc}
   */
  public boolean isPrintReadmeSet() {
    return ogPrintReadme.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getPrintReadme() {
    return ogPrintReadme.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawPrintReadme() {
    return ogPrintReadme.getRawValue();
  }
  
  public BooleanOption getPrintReadmeOption() {
    return ogPrintReadme;
  }
  
// Option PrintBashCompletion.
// Aliases: [--print-bash-completion]
  
  /**
   * {@inheritDoc}
   */
  public boolean isPrintBashCompletionSet() {
    return ogPrintBashCompletion.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getPrintBashCompletion() {
    return ogPrintBashCompletion.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawPrintBashCompletion() {
    return ogPrintBashCompletion.getRawValue();
  }
  
  public BooleanOption getPrintBashCompletionOption() {
    return ogPrintBashCompletion;
  }
  
// Option Help.
// Aliases: [-h, --help]
  
  /**
   * {@inheritDoc}
   */
  public boolean isHelpSet() {
    return ogHelp.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getHelp() {
    return ogHelp.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawHelp() {
    return ogHelp.getRawValue();
  }
  
  public BooleanOption getHelpOption() {
    return ogHelp;
  }
  
// Option Time.
// Aliases: [-t, --time]
  
  /**
   * {@inheritDoc}
   */
  public boolean isTimeSet() {
    return ogTime.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getTime() {
    return ogTime.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawTime() {
    return ogTime.getRawValue();
  }
  
  public BooleanOption getTimeOption() {
    return ogTime;
  }
  
// Option Typecheck.
// Aliases: [-tc, --typecheck]
  
  /**
   * {@inheritDoc}
   */
  public boolean isTypecheckSet() {
    return ogTypecheck.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getTypecheck() {
    return ogTypecheck.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawTypecheck() {
    return ogTypecheck.getRawValue();
  }
  
  public BooleanOption getTypecheckOption() {
    return ogTypecheck;
  }
  
// Option Informal.
// Aliases: [-i, --informal]
  
  /**
   * {@inheritDoc}
   */
  public boolean isInformalSet() {
    return ogInformal.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getInformal() {
    return ogInformal.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawInformal() {
    return ogInformal.getRawValue();
  }
  
  public BooleanOption getInformalOption() {
    return ogInformal;
  }
  
// Option Formal.
// Aliases: [-f, --formal]
  
  /**
   * {@inheritDoc}
   */
  public boolean isFormalSet() {
    return ogFormal.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getFormal() {
    return ogFormal.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawFormal() {
    return ogFormal.getRawValue();
  }
  
  public BooleanOption getFormalOption() {
    return ogFormal;
  }
  
// Option CheckInformal.
// Aliases: [-ci, --check-informal]
  
  /**
   * {@inheritDoc}
   */
  public boolean isCheckInformalSet() {
    return ogCheckInformal.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getCheckInformal() {
    return ogCheckInformal.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawCheckInformal() {
    return ogCheckInformal.getRawValue();
  }
  
  public BooleanOption getCheckInformalOption() {
    return ogCheckInformal;
  }
  
// Option CheckFormal.
// Aliases: [-cf, --check-formal]
  
  /**
   * {@inheritDoc}
   */
  public boolean isCheckFormalSet() {
    return ogCheckFormal.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getCheckFormal() {
    return ogCheckFormal.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawCheckFormal() {
    return ogCheckFormal.getRawValue();
  }
  
  public BooleanOption getCheckFormalOption() {
    return ogCheckFormal;
  }
  
// Option CheckConsistency.
// Aliases: [-cc, --check-consistency]
  
  /**
   * {@inheritDoc}
   */
  public boolean isCheckConsistencySet() {
    return ogCheckConsistency.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getCheckConsistency() {
    return ogCheckConsistency.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawCheckConsistency() {
    return ogCheckConsistency.getRawValue();
  }
  
  public BooleanOption getCheckConsistencyOption() {
    return ogCheckConsistency;
  }
  
// Option Debug.
// Aliases: [-d, --debug]
  
  /**
   * {@inheritDoc}
   */
  public boolean isDebugSet() {
    return ogDebug.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getDebug() {
    return ogDebug.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawDebug() {
    return ogDebug.getRawValue();
  }
  
  public BooleanOption getDebugOption() {
    return ogDebug;
  }
  
// Option ReadFromStdin.
// Aliases: [-]
  
  /**
   * {@inheritDoc}
   */
  public boolean isReadFromStdinSet() {
    return ogReadFromStdin.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getReadFromStdin() {
    return ogReadFromStdin.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawReadFromStdin() {
    return ogReadFromStdin.getRawValue();
  }
  
  public BooleanOption getReadFromStdinOption() {
    return ogReadFromStdin;
  }
  
// Option GenClassDic.
// Aliases: [-gcd, --gen-class-dic]
  
  /**
   * {@inheritDoc}
   */
  public boolean isGenClassDicSet() {
    return ogGenClassDic.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getGenClassDic() {
    return ogGenClassDic.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawGenClassDic() {
    return ogGenClassDic.getRawValue();
  }
  
  public BooleanOption getGenClassDicOption() {
    return ogGenClassDic;
  }
  
// Option Graph.
// Aliases: [-g, --graph]
  
  /**
   * {@inheritDoc}
   */
  public boolean isGraphSet() {
    return ogGraph.hasValue();
  }
  

  /** {@inheritDoc} */
  public Graph getGraph() {
    return Graph.get(ogGraph.getValue());
  }

  /** {@inheritDoc} */
  public String getRawGraph() {
    return ogGraph.getRawValue();
  }
  
  public EnumOption getGraphOption() {
    return ogGraph;
  }
  
// Option Version.
// Aliases: [-v, -version, --version]
  
  /**
   * {@inheritDoc}
   */
  public boolean isVersionSet() {
    return ogVersion.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getVersion() {
    return ogVersion.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawVersion() {
    return ogVersion.getRawValue();
  }
  
  public BooleanOption getVersionOption() {
    return ogVersion;
  }
  
// Option SourceFiles.
// Aliases: []
  
  /**
   * {@inheritDoc}
   */
  public boolean isSourceFilesSet() {
    return ogSourceFiles.hasValue();
  }
  
  /** {@inheritDoc} */
  public List<java.io.File> getSourceFiles() {
    return ogSourceFiles.getValue();
  }

  /** {@inheritDoc} */
  public List<java.io.File> getRawSourceFiles() {
    return ogSourceFiles.getRawValue();
  }
  
  public FileListOption getSourceFilesOption() {
    return ogSourceFiles;
  }
  
}
