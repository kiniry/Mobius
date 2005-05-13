import java.util.Properties;

class DemonstrationProver implements ProverInterface
{
  static {
    System.loadLibrary("demoprover");
  }

  // start_solver : unit -> int
  public native int demo_start_prover();

  public ProverResponse start_prover() {
    return new ProverResponse(demo_start_prover());
  }

  // set_flags : string -> int
  public native int demo_set_prover_resource_flags(String properties);

  public ProverResponse set_prover_resource_flags(Properties properties) {
    assert false;
    return null;
  }

  // decaration : string -> int
  public native int demo_signature(String signature);

  public ProverResponse signature(Signature signature) {
    assert false;
    return null;
  }

  // add_axiom : string -> int
  public native int demo_declare_axiom(String axiom);

  public ProverResponse declare_axiom(Formula formula) {
    assert false;
    return null;
  }

  // add_assertion : string -> int
  public native int demo_make_assumption(String formula);

  public ProverResponse make_assumption(Formula formula) {
    assert false;
    return null;
  }

  // backtrack : int -> int
  public native int demo_retract_assumption(int count);

  public ProverResponse retract_assumption(int count) {
    assert false;
    return null;
  }

  // query : string -> int
  public native int demo_is_valid(String formula, String properties);

  public ProverResponse is_valid(Formula formula,
                                 Properties properties) {
    assert false;
    return null;
  }

  // stop_solver : unit -> int
  public native int demo_stop_prover();

  public ProverResponse stop_prover() {
    return new ProverResponse(demo_stop_prover());
  }

  // quick-and-dirty unit test for starting and stopping prover
  public static void main(String[] args) {
    DemonstrationProver prover = new DemonstrationProver();
    prover.start_prover();
    System.out.println("Prover started.");
    prover.stop_prover();
    System.out.println("Prover stopped.");
  }
}
