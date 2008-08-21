/**
 * Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon;

import ie.ucd.commandline.actions.TriggersBoolean;
import ie.ucd.commandline.actions.TriggersString;
import ie.ucd.commandline.constraints.MutuallyExclusiveConstraint;
import ie.ucd.commandline.constraints.ORConstraint;
import ie.ucd.commandline.constraints.RequiresConstraint;
import ie.ucd.commandline.options.BooleanDefaultOption;
import ie.ucd.commandline.options.InvalidOptionsSetException;
import ie.ucd.commandline.options.StringDefaultOption;
import ie.ucd.commandline.parser.CommandlineParser;
import ie.ucd.commandline.parser.CommandlineParser.SortingOption;

public final class CLP {
  
  /** Prevent instantiation of CLP. */
  private CLP() { }
	
  public static CommandlineParser commandlineParser() throws InvalidOptionsSetException {
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
    pp.addOptionName("-p");
    pp.addOptionName("-print");
    pp.addOptionName("--print");
    pp.setArgName("TYPE");
    pp.setHelpString("Print the parsed input in the given format. TXT for plain-text, HTML for html generation of informal charts, DIC to generate the class dictionary, IIG for the informal class inheritance graph. See the manpage or README.txt for more information and a list of all printing options.");
    cp.addOption(pp);
    
    StringDefaultOption ppo = new StringDefaultOption();
    ppo.setOptionID("2.1");
    ppo.addOptionName("-po");
    ppo.addOptionName("--print-output");
    ppo.setArgName("FILE");
    ppo.setHelpString("Print output to the given file instead of to stdout.");
    ppo.addConstraint(new ORConstraint(new RequiresConstraint("2.1", "2"), new RequiresConstraint("2.1", "2.2")));
    cp.addOption(ppo);
    
    BooleanDefaultOption p = new BooleanDefaultOption();
    p.setOptionID("2.2");
    p.addOptionName("-pp");
    p.addOptionName("--pretty-print");
    p.setHelpString("Pretty-print the parsed input. This is equivalent to -p=TXT.");
    p.addConstraint(new MutuallyExclusiveConstraint("2", "2.2"));
    p.addAction(new TriggersString("2.2", "2", "TXT"));
    cp.addOption(p);
    
    
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
    
    /*StringDefaultOption cg = new StringDefaultOption();
    cg.setOptionID("5");
    cg.addOptionName("-cg");
    cg.setHelpString("Print class and cluster graph in the .dot file format.");
    cg.setHidden(); //Hidden until revisiting
    cp.addOption(cg);
    
    StringDefaultOption ig = new StringDefaultOption();
    ig.setOptionID("6");
    ig.addOptionName("-ig");
    ig.setHelpString("Print class inheritance graph in the .dot file format.");
    ig.setHidden(); //Hidden until revisiting
    cp.addOption(ig);*/
    
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
    
    BooleanDefaultOption genClassDicWhenPrinting = new BooleanDefaultOption();
    genClassDicWhenPrinting.setOptionID("77");
    genClassDicWhenPrinting.addOptionName("-gcd");
    genClassDicWhenPrinting.addOptionName("--gen-class-dic");
    genClassDicWhenPrinting.setHelpString("Generate the class dictionary when printing.");
    genClassDicWhenPrinting.setByDefault();
    genClassDicWhenPrinting.setHidden();
    cp.addOption(genClassDicWhenPrinting);
    
    BooleanDefaultOption noGenClassDicWhenPrinting = new BooleanDefaultOption();
    noGenClassDicWhenPrinting.setOptionID("77.1");
    noGenClassDicWhenPrinting.addOptionName("-ngcd");
    noGenClassDicWhenPrinting.addOptionName("--no-gen-class-dic");
    noGenClassDicWhenPrinting.setHelpString("Do not generate the class dictionary when printing.");
    noGenClassDicWhenPrinting.addAction(new TriggersBoolean("77.1", "77", false));
    cp.addOption(noGenClassDicWhenPrinting);
    
    StringDefaultOption g = new StringDefaultOption();
    g.setOptionID("100");
    g.addOptionName("-g");
    g.addOptionName("-graph");
    g.addOptionName("--graph");
    g.setArgName("TYPE");
    g.setHelpString("Display the chosen graph type. ICG for informal clustering graph, IIG for informal inheritance graph.");
    cp.addOption(g);
    
    BooleanDefaultOption printMan = new BooleanDefaultOption();
    printMan.setOptionID("99999");
    printMan.setHidden();
    printMan.addOptionName("-pm");
    printMan.addOptionName("--print-man");
    printMan.setHelpString("Print available options in man-page format");
    cp.addOption(printMan);
    
    BooleanDefaultOption printReadme = new BooleanDefaultOption();
    printReadme.setOptionID("99999.1");
    printReadme.setHidden();
    printReadme.addOptionName("-pr");
    printReadme.addOptionName("--print-readme");
    printReadme.setHelpString("Print available options in readme format");
    cp.addOption(printReadme);
    
    BooleanDefaultOption printBashCompletion = new BooleanDefaultOption();
    printBashCompletion.setOptionID("99999.2");
    printBashCompletion.setHidden();
    printBashCompletion.addOptionName("-pbc");
    printBashCompletion.addOptionName("--print-bash-completion");
    printBashCompletion.setHelpString("Print bash completion script for available options.");
    cp.addOption(printBashCompletion);
    
    BooleanDefaultOption version = new BooleanDefaultOption();
    version.setOptionID("999v");
    version.addOptionName("-v");
    version.addOptionName("--version");
    version.setHelpString("Print BONc version and exit.");
    cp.addOption(version);
    
    return cp;
  }
  
}
