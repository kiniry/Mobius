package freeboogie.vcgen;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.logging.Logger;

import freeboogie.ast.Declaration;
import freeboogie.ast.Implementation;
import freeboogie.backend.Prover;
import freeboogie.backend.ProverException;
import freeboogie.backend.SmtTerm;
import freeboogie.backend.Term;
import freeboogie.backend.TermBuilder;
import freeboogie.tc.TcInterface;

/**
 * A facade for the {@code freeboogie.vcgen} package.
 *
 * The user can hand over an AST for preprocessing and then ask
 * for individual implementations to be checked. The prover to be
 * used is given by the user.
 */
public class VcGenerator<T extends Term<T>> {
  /* IMPLEMENTATION
   *
   * The phases of VC generation are:
   *  (1) make graphs reducible TODO
   *  (2) infer invariants TODO
   *  (3) cut loops 
   *  (4) desugar calls 
   *  (5) desugar havoc
   *  (6) desugar where clauses TODO
   *  (7) desugar specifications 
   *  (8) make passive 
   *  (9) desugar maps, if the prover doesn't know about arrays
   * (10) desugar uniq on constants TODO
   * (11) desugar <: is prover doesn't know it TODO
   * (12) strongest postcondition
   */

  private static final Logger log = Logger.getLogger("freeboogie.vcgen");

  private Declaration ast;
  private TcInterface tc;

  private HavocMaker havocMaker;
  private LoopCutter loopCutter;
  private CallDesugarer callDesugarer;
  private HavocDesugarer havocDesugarer;
  private SpecDesugarer specDesugarer;
  private Passivator passivator;
  private MapRemover mapRemover;
  private FunctionRegisterer functionRegisterer;
  private AxiomSender<T> axiomSender;
  private final FormulaProcessor<T> processor;

  private StrongestPostcondition<T> sp;

  private Prover<T> prover;
  private TermBuilder<T> builder;

  private Set<T> lowLevelAxiomBag;


  public VcGenerator(FormulaProcessor<T> processor) {
    havocMaker = new HavocMaker();
    loopCutter = new LoopCutter();
    callDesugarer = new CallDesugarer();
    havocDesugarer = new HavocDesugarer(); 
    specDesugarer = new SpecDesugarer();
    passivator = new Passivator(false);
    mapRemover = new MapRemover();
    functionRegisterer = new FunctionRegisterer();
    axiomSender = new AxiomSender<T>();
    sp = new StrongestPostcondition<T>();
    lowLevelAxiomBag = new HashSet<T>(13);
    this.processor = processor;
  }

  public void setProver(Prover<T> prover) throws ProverException {
    this.prover = prover;
    prover.push();
    preverify();
  }

  /**
   * Simplify {@code d} to a form where strongest postcondition
   * can be computed.
   */
  public Declaration process(Declaration d, TcInterface tc)
  throws ProverException {
    this.tc = tc;
    ast = havocMaker.process(d, tc);
    ast = loopCutter.process(ast, tc);
    ast = callDesugarer.process(ast, tc);
    ast = havocDesugarer.process(ast, tc);
    ast = specDesugarer.process(ast, tc);
    ast = passivator.process(ast, tc);
    ast = mapRemover.process(ast, tc);
    preverify();
    return ast;
  }

  /**
   * Compute strongest postcondition and query the prover. This
   * {@code implementation} must be part the AST last processed.
   * Also, a prover must have been set.
   */
  public boolean verify(Implementation implementation, boolean removeSharing) throws ProverException {
    assert prover != null && ast != null;
    sp.setFlowGraph(tc.getFlowGraph(implementation));
    T vc = sp.vc();
    if (removeSharing) {
      log.fine("Original size: " + DeSharifier.getSize((SmtTerm)(Object)vc, new HashMap<SmtTerm,Integer>()));
      vc = processor.process(vc);
      log.fine("Processed size: " + DeSharifier.getSize(((SmtTerm)(Object)vc), new HashMap<SmtTerm,Integer>()));
    }
    lowLevelAxiomBag.clear();
    vc.collectAxioms(lowLevelAxiomBag);
    if (removeSharing) {
      lowLevelAxiomBag.addAll(processor.getAxioms(vc));
    }
    prover.push();
    for (T t : lowLevelAxiomBag) prover.assume(t);
    boolean result = prover.isValid(vc);
    prover.pop();
    return result;
  }

  // === helpers ===
  private void preverify() throws ProverException {
    if (prover == null || ast == null) return;

    // prepare fields for verify() to use
    builder = prover.getBuilder();
    sp.setBuilder(builder);
    processor.setBuilder(builder);
    builder.setTypeChecker(tc);
    functionRegisterer.setBuilder(builder);
    axiomSender.setProver(prover);

    // register function name symbols with the builder
    builder.popDef();
    functionRegisterer.process(ast, tc);
    builder.pushDef();

    // send global axioms
    prover.pop();
    axiomSender.process(ast);
    prover.push();
  }
}
