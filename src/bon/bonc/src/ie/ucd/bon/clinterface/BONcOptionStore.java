package ie.ucd.bon.clinterface;

import ie.ucd.clops.runtime.options.CLOPSErrorOption;
import ie.ucd.clops.runtime.options.OptionGroup;
import ie.ucd.clops.runtime.options.OptionStore;
import ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException;
import java.util.List;
import java.io.File;
import ie.ucd.clops.runtime.options.EnumOption;
import ie.ucd.clops.runtime.options.FileOption;
import ie.ucd.clops.runtime.options.BooleanOption;
import ie.ucd.clops.runtime.options.FileListOption;

public class BONcOptionStore extends OptionStore implements BONcOptionsInterface {

  private final BooleanOption ogtypecheck;
  private final BooleanOption ogno_typecheck;
  private final EnumOption ogprint;
  private final FileOption ogprint_output;
  private final BooleanOption ogpretty_print;
  private final BooleanOption oghelp;
  private final BooleanOption oghidden_help;
  private final BooleanOption ogtime;
  private final BooleanOption oginformal;
  private final BooleanOption ogformal;
  private final BooleanOption ogcheck_informal;
  private final BooleanOption ogcheck_formal;
  private final BooleanOption ogcheck_consistency;
  private final BooleanOption ogno_check_consistency;
  private final BooleanOption ogdebug;
  private final BooleanOption oggen_class_dic;
  private final BooleanOption ogno_gen_class_dic;
  private final EnumOption oggraph;
  private final BooleanOption ogversion;
  private final FileListOption ogSourceFiles;
  private final CLOPSErrorOption CLOPSERROROPTION;

  public BONcOptionStore() throws InvalidOptionPropertyValueException {

    //Options
    ogtypecheck = new BooleanOption("typecheck", "(?:-tc)|(?:--typecheck)");
    addOption(ogtypecheck);
    ogtypecheck.setProperty("default", "true");
    ogno_typecheck = new BooleanOption("no_typecheck", "(?:-ntc)|(?:--no-typecheck)");
    addOption(ogno_typecheck);
    ogno_typecheck.setProperty("default", "false");
    ogprint = new EnumOption("print", "(?:-p)|(?:--print)");
    addOption(ogprint);
    ogprint.setProperty("choices", "txt,html,xhtml,dic");
    ogprint.setProperty("casesensitive", "false");
    ogprint_output = new FileOption("print_output", "(?:-po)|(?:--print-output)");
    addOption(ogprint_output);
    ogprint_output.setProperty("canbedir", "false");
    ogpretty_print = new BooleanOption("pretty_print", "(?:-pp)|(?:--pretty-print)");
    addOption(ogpretty_print);
    oghelp = new BooleanOption("help", "(?:-h)|(?:--help)");
    addOption(oghelp);
    oghidden_help = new BooleanOption("hidden_help", "(?:-hh)|(?:--hidden-help)");
    addOption(oghidden_help);
    ogtime = new BooleanOption("time", "(?:-t)|(?:--time)");
    addOption(ogtime);
    oginformal = new BooleanOption("informal", "(?:-i)|(?:--informal)");
    addOption(oginformal);
    ogformal = new BooleanOption("formal", "(?:-f)|(?:--formal)");
    addOption(ogformal);
    ogcheck_informal = new BooleanOption("check_informal", "(?:-ci)|(?:--check-informal)");
    addOption(ogcheck_informal);
    ogcheck_formal = new BooleanOption("check_formal", "(?:-cf)|(?:--check-formal)");
    addOption(ogcheck_formal);
    ogcheck_consistency = new BooleanOption("check_consistency", "(?:-cc)|(?:--check-consistency)");
    addOption(ogcheck_consistency);
    ogno_check_consistency = new BooleanOption("no_check_consistency", "(?:-ncc)|(?:--no-check-consistency)");
    addOption(ogno_check_consistency);
    ogdebug = new BooleanOption("debug", "(?:-d)|(?:--debug)");
    addOption(ogdebug);
    oggen_class_dic = new BooleanOption("gen_class_dic", "(?:-gcd)|(?:--gen-class-dic)");
    addOption(oggen_class_dic);
    ogno_gen_class_dic = new BooleanOption("no_gen_class_dic", "(?:-ngcd)|(?:--no-gen-class-dic)");
    addOption(ogno_gen_class_dic);
    oggraph = new EnumOption("graph", "(?:-g)|(?:--graph)");
    addOption(oggraph);
    oggraph.setProperty("choices", "icg,iig");
    oggraph.setProperty("casesensitive", "false");
    ogversion = new BooleanOption("version", "(?:-v)|(?:--version)");
    addOption(ogversion);
    ogSourceFiles = new FileListOption("SourceFiles", "");
    addOption(ogSourceFiles);
    ogSourceFiles.setProperty("canbedir", "false");
    ogSourceFiles.setProperty("mustexist", "true");
  
    CLOPSERROROPTION = new ie.ucd.clops.runtime.options.CLOPSErrorOption();
    addOption(CLOPSERROROPTION);
  
    //Option groups
    final OptionGroup ogoption = new OptionGroup("option");
    addOptionGroup(ogoption);
    final OptionGroup ogAllOptions = new OptionGroup("AllOptions");
    addOptionGroup(ogAllOptions);
    
    //Setup groupings
    ogoption.addOptionOrGroup(ogprint_output);
    ogoption.addOptionOrGroup(ogcheck_consistency);
    ogoption.addOptionOrGroup(ogno_check_consistency);
    ogoption.addOptionOrGroup(ogdebug);
    ogoption.addOptionOrGroup(ogprint);
    ogoption.addOptionOrGroup(ogformal);
    ogoption.addOptionOrGroup(ogtime);
    ogoption.addOptionOrGroup(oggraph);
    ogoption.addOptionOrGroup(ogpretty_print);
    ogoption.addOptionOrGroup(oginformal);
    ogoption.addOptionOrGroup(ogno_gen_class_dic);
    ogoption.addOptionOrGroup(oggen_class_dic);
    ogoption.addOptionOrGroup(ogcheck_formal);
    //AllOptions group
    ogAllOptions.addOptionOrGroup(ogtypecheck);
    ogAllOptions.addOptionOrGroup(ogno_typecheck);
    ogAllOptions.addOptionOrGroup(ogprint);
    ogAllOptions.addOptionOrGroup(ogprint_output);
    ogAllOptions.addOptionOrGroup(ogpretty_print);
    ogAllOptions.addOptionOrGroup(oghelp);
    ogAllOptions.addOptionOrGroup(oghidden_help);
    ogAllOptions.addOptionOrGroup(ogtime);
    ogAllOptions.addOptionOrGroup(oginformal);
    ogAllOptions.addOptionOrGroup(ogformal);
    ogAllOptions.addOptionOrGroup(ogcheck_informal);
    ogAllOptions.addOptionOrGroup(ogcheck_formal);
    ogAllOptions.addOptionOrGroup(ogcheck_consistency);
    ogAllOptions.addOptionOrGroup(ogno_check_consistency);
    ogAllOptions.addOptionOrGroup(ogdebug);
    ogAllOptions.addOptionOrGroup(oggen_class_dic);
    ogAllOptions.addOptionOrGroup(ogno_gen_class_dic);
    ogAllOptions.addOptionOrGroup(oggraph);
    ogAllOptions.addOptionOrGroup(ogversion);
    ogAllOptions.addOptionOrGroup(ogSourceFiles);
  }
  
// Option typecheck.
// Aliases: [-tc, --typecheck]
  
  /**
   * {@inheritDoc}
   */
  public boolean istypecheckSet() {
    return ogtypecheck.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean gettypecheck() {
    return ogtypecheck.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawtypecheck() {
    return ogtypecheck.getRawValue();
  }
  
  public BooleanOption gettypecheckOption() {
    return ogtypecheck;
  }
  
// Option no_typecheck.
// Aliases: [-ntc, --no-typecheck]
  
  /**
   * {@inheritDoc}
   */
  public boolean isno_typecheckSet() {
    return ogno_typecheck.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getno_typecheck() {
    return ogno_typecheck.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawno_typecheck() {
    return ogno_typecheck.getRawValue();
  }
  
  public BooleanOption getno_typecheckOption() {
    return ogno_typecheck;
  }
  
// Option print.
// Aliases: [-p, --print]
  
  /**
   * {@inheritDoc}
   */
  public boolean isprintSet() {
    return ogprint.hasValue();
  }
  

  /** {@inheritDoc} */
  public print getprint() {
    return print.get(ogprint.getValue());
  }

  /** {@inheritDoc} */
  public String getRawprint() {
    return ogprint.getRawValue();
  }
  
  public EnumOption getprintOption() {
    return ogprint;
  }
  
// Option print_output.
// Aliases: [-po, --print-output]
  
  /**
   * {@inheritDoc}
   */
  public boolean isprint_outputSet() {
    return ogprint_output.hasValue();
  }
  
  /** {@inheritDoc} */
  public File getprint_output() {
    return ogprint_output.getValue();
  }

  /** {@inheritDoc} */
  public File getRawprint_output() {
    return ogprint_output.getRawValue();
  }
  
  public FileOption getprint_outputOption() {
    return ogprint_output;
  }
  
// Option pretty_print.
// Aliases: [-pp, --pretty-print]
  
  /**
   * {@inheritDoc}
   */
  public boolean ispretty_printSet() {
    return ogpretty_print.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getpretty_print() {
    return ogpretty_print.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawpretty_print() {
    return ogpretty_print.getRawValue();
  }
  
  public BooleanOption getpretty_printOption() {
    return ogpretty_print;
  }
  
// Option help.
// Aliases: [-h, --help]
  
  /**
   * {@inheritDoc}
   */
  public boolean ishelpSet() {
    return oghelp.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean gethelp() {
    return oghelp.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawhelp() {
    return oghelp.getRawValue();
  }
  
  public BooleanOption gethelpOption() {
    return oghelp;
  }
  
// Option hidden_help.
// Aliases: [-hh, --hidden-help]
  
  /**
   * {@inheritDoc}
   */
  public boolean ishidden_helpSet() {
    return oghidden_help.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean gethidden_help() {
    return oghidden_help.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawhidden_help() {
    return oghidden_help.getRawValue();
  }
  
  public BooleanOption gethidden_helpOption() {
    return oghidden_help;
  }
  
// Option time.
// Aliases: [-t, --time]
  
  /**
   * {@inheritDoc}
   */
  public boolean istimeSet() {
    return ogtime.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean gettime() {
    return ogtime.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawtime() {
    return ogtime.getRawValue();
  }
  
  public BooleanOption gettimeOption() {
    return ogtime;
  }
  
// Option informal.
// Aliases: [-i, --informal]
  
  /**
   * {@inheritDoc}
   */
  public boolean isinformalSet() {
    return oginformal.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getinformal() {
    return oginformal.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawinformal() {
    return oginformal.getRawValue();
  }
  
  public BooleanOption getinformalOption() {
    return oginformal;
  }
  
// Option formal.
// Aliases: [-f, --formal]
  
  /**
   * {@inheritDoc}
   */
  public boolean isformalSet() {
    return ogformal.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getformal() {
    return ogformal.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawformal() {
    return ogformal.getRawValue();
  }
  
  public BooleanOption getformalOption() {
    return ogformal;
  }
  
// Option check_informal.
// Aliases: [-ci, --check-informal]
  
  /**
   * {@inheritDoc}
   */
  public boolean ischeck_informalSet() {
    return ogcheck_informal.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getcheck_informal() {
    return ogcheck_informal.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawcheck_informal() {
    return ogcheck_informal.getRawValue();
  }
  
  public BooleanOption getcheck_informalOption() {
    return ogcheck_informal;
  }
  
// Option check_formal.
// Aliases: [-cf, --check-formal]
  
  /**
   * {@inheritDoc}
   */
  public boolean ischeck_formalSet() {
    return ogcheck_formal.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getcheck_formal() {
    return ogcheck_formal.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawcheck_formal() {
    return ogcheck_formal.getRawValue();
  }
  
  public BooleanOption getcheck_formalOption() {
    return ogcheck_formal;
  }
  
// Option check_consistency.
// Aliases: [-cc, --check-consistency]
  
  /**
   * {@inheritDoc}
   */
  public boolean ischeck_consistencySet() {
    return ogcheck_consistency.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getcheck_consistency() {
    return ogcheck_consistency.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawcheck_consistency() {
    return ogcheck_consistency.getRawValue();
  }
  
  public BooleanOption getcheck_consistencyOption() {
    return ogcheck_consistency;
  }
  
// Option no_check_consistency.
// Aliases: [-ncc, --no-check-consistency]
  
  /**
   * {@inheritDoc}
   */
  public boolean isno_check_consistencySet() {
    return ogno_check_consistency.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getno_check_consistency() {
    return ogno_check_consistency.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawno_check_consistency() {
    return ogno_check_consistency.getRawValue();
  }
  
  public BooleanOption getno_check_consistencyOption() {
    return ogno_check_consistency;
  }
  
// Option debug.
// Aliases: [-d, --debug]
  
  /**
   * {@inheritDoc}
   */
  public boolean isdebugSet() {
    return ogdebug.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getdebug() {
    return ogdebug.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawdebug() {
    return ogdebug.getRawValue();
  }
  
  public BooleanOption getdebugOption() {
    return ogdebug;
  }
  
// Option gen_class_dic.
// Aliases: [-gcd, --gen-class-dic]
  
  /**
   * {@inheritDoc}
   */
  public boolean isgen_class_dicSet() {
    return oggen_class_dic.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getgen_class_dic() {
    return oggen_class_dic.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawgen_class_dic() {
    return oggen_class_dic.getRawValue();
  }
  
  public BooleanOption getgen_class_dicOption() {
    return oggen_class_dic;
  }
  
// Option no_gen_class_dic.
// Aliases: [-ngcd, --no-gen-class-dic]
  
  /**
   * {@inheritDoc}
   */
  public boolean isno_gen_class_dicSet() {
    return ogno_gen_class_dic.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getno_gen_class_dic() {
    return ogno_gen_class_dic.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawno_gen_class_dic() {
    return ogno_gen_class_dic.getRawValue();
  }
  
  public BooleanOption getno_gen_class_dicOption() {
    return ogno_gen_class_dic;
  }
  
// Option graph.
// Aliases: [-g, --graph]
  
  /**
   * {@inheritDoc}
   */
  public boolean isgraphSet() {
    return oggraph.hasValue();
  }
  

  /** {@inheritDoc} */
  public graph getgraph() {
    return graph.get(oggraph.getValue());
  }

  /** {@inheritDoc} */
  public String getRawgraph() {
    return oggraph.getRawValue();
  }
  
  public EnumOption getgraphOption() {
    return oggraph;
  }
  
// Option version.
// Aliases: [-v, --version]
  
  /**
   * {@inheritDoc}
   */
  public boolean isversionSet() {
    return ogversion.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getversion() {
    return ogversion.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawversion() {
    return ogversion.getRawValue();
  }
  
  public BooleanOption getversionOption() {
    return ogversion;
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
