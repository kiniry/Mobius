package umbra.annot.bcclass.attributes;

public class LoopSpecification implements BCAttribute {
	SingleLoopSpecification[] loopSpecs;
	
	public LoopSpecification(SingleLoopSpecification[] _loopSpecs) {
		loopSpecs = _loopSpecs;
	}

	public SingleLoopSpecification[] getLoopSpecifications() {
		return loopSpecs;
	}
	
	public String printCode() {
		System.out.println("LoopSpec - printCode");
		String cd = "";
		for (int i = 0; i < loopSpecs.length; i++) {
			cd = cd + loopSpecs[i].printCode();
		}
		return cd;
	}
}
