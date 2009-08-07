package freeboogie.vcgen;

import java.util.Set;

import com.google.common.collect.Sets;
import genericutils.Logger;

import freeboogie.ast.*;
import freeboogie.backend.*;
import freeboogie.cli.FbCliOptionsInterface;
import freeboogie.tc.TcInterface;

import static freeboogie.cli.FbCliOptionsInterface.LogCategories;
import static freeboogie.cli.FbCliOptionsInterface.LogLevel;
import static freeboogie.cli.FbCliOptionsInterface.ReportLevel;
import static freeboogie.cli.FbCliOptionsInterface.ReportOn;

/**
  Checks the correctness of each implementation and reports
  the results.

  The results are reported to the logger "out".

  Although this class is implemented by extending {@code
  Transformer} it does not modify the AST.

  Before using it, you should {@code initialize()} it by passing
  in options. This will configure the main VC method (like SP vs
  WP), the stages that are applied afterwards to modify the logic
  formula, and the theorem prover which is queried.

  This class handles restarting the prover in case a
  communication problem, a segfault, or some other horrible
  situation arises.
 */
public class VcGenerator extends Transformer {
  private Logger<LogCategories, LogLevel> log = 
    Logger.<LogCategories, LogLevel>get("log");
  private Logger<ReportOn, ReportLevel> out =
    Logger.<ReportOn, ReportLevel>get("out");

  public void log(String s) {
    log.say(LogCategories.VCGEN, LogLevel.INFO, s);
  }

  private Prover<SmtTerm> prover;
  private TermBuilder<SmtTerm> builder;
  private ACalculus<SmtTerm> vcgen;
  private FunctionRegisterer functionRegisterer;
  private AxiomSender<SmtTerm> axiomSender;
  private Set<SmtTerm> lowLevelAxiomBag;

  private StringBuilder sb = new StringBuilder();
  private FbCliOptionsInterface opt;

  public void reinitialize() { 
    log.say(
        LogCategories.VCGEN,
        LogLevel.WARNING,
        "Reinitializing VcGenerator.");
    if (prover != null) prover.terminate();
    prover = null;
    initialize(opt); 
  }

  public void initialize(FbCliOptionsInterface opt) {
    this.opt = opt;
    switch (opt.getVcMethodOpt()) {
      case WP: vcgen = new WeakestPrecondition<SmtTerm>(); break;
      default: vcgen = new StrongestPostcondition<SmtTerm>(); break;
    }
    vcgen.assumeAsserts(opt.isAssumeAssertsSet());
    prover = new YesSmtProver();
    try {
      switch (opt.getProverOpt()) {
        case SIMPLIFY: 
          prover = new SimplifyProver(
              opt.getProverCommandLineOpt().split("\\s+"));
          break;
      }
    } catch (ProverException e) {
      out.say(
          ReportOn.MAIN, 
          ReportLevel.NORMAL, 
          "I can't start the prover. All querries will pass.");
      log.say(
          LogCategories.VCGEN, 
          LogLevel.WARNING,
          "ProverException: " + e);
    }
    try { prover.push(); }
    catch (ProverException e) {
      out.say(
          ReportOn.MAIN,
          ReportLevel.NORMAL,
          "The prover can't hear me. Falling back to my dear YesMan.");
      prover = new YesSmtProver();
      try { prover.push(); } catch (ProverException f) { assert false; }
    }
    functionRegisterer = new FunctionRegisterer();
    axiomSender = new AxiomSender<SmtTerm>();
    lowLevelAxiomBag = Sets.newHashSet();
  }

  @Override
  public Program process(Program p, TcInterface tc) {
    // prepare for the verification of each implementation
    vcgen.typeChecker(tc);
    builder = prover.getBuilder();
    builder.setTypeChecker(tc);
    vcgen.setBuilder(builder);
    functionRegisterer.setBuilder(builder);
    axiomSender.setProver(prover);

    // register function name symbols with the builder
    builder.popDef();
    functionRegisterer.process(p.ast, tc);
    builder.pushDef();

    // send global axioms
    try {
      prover.pop();
      axiomSender.process(p.ast);
      prover.push();
    } catch (ProverException e) {
      out.say(
          ReportOn.MAIN,
          ReportLevel.NORMAL,
          "The prover can't handle " + p.fileName + ". Skipping.");
      prover.terminate();
      reinitialize();
      return p;
    }
    log("Sent global axioms for file " + p.fileName + ".");

    // do the verification
    Ast x = p.ast.eval(this);
    assert x == p.ast;
    log("Finished checking file " + p.fileName + ".");
    return p;
  }

  @Override
  public void see(
      Implementation implementation, 
      Attribute attr, 
      Signature sig, 
      Body body, 
      Declaration tail
  ) {
    log("Checking implementation " + sig.getName() + " at " + sig.loc());
    vcgen.setCurrentBody(body);
    SmtTerm vc = vcgen.vc();
    lowLevelAxiomBag.clear();
    vc.collectAxioms(lowLevelAxiomBag);
    sb.setLength(0);
    try {
      prover.push();
      for (SmtTerm t : lowLevelAxiomBag) prover.assume(t);
      sb.append(prover.isValid(vc)? " OK" : "NOK");
      prover.pop();
    } catch (ProverException e) {
      sb.append("  ?");
      reinitialize();
    }
    sb.append(": ");
    sb.append(sig.getName());
    sb.append(" at ");
    sb.append(sig.loc().toString());
    out.say(ReportOn.MAIN, ReportLevel.QUIET, sb.toString());
  }
}

