package annot.bcclass.attributes;

public class LoopSpecification implements BCAttribute {
	SingleLoopSpecification[] loopSpecs;
	
	public LoopSpecification(SingleLoopSpecification[] _loopSpecs) {
		loopSpecs = _loopSpecs;
	}

	public SingleLoopSpecification[] getLoopSpecifications() {
		return loopSpecs;
	}
	
	public SingleLoopSpecification getAtPC(int pc, int n) {
		for (int i=0; i<loopSpecs.length; i++)
			if (loopSpecs[i].pcIndex == pc) {
				if (--n == 0)
					return loopSpecs[i];
			}
		System.err.println("(LoopSpecification) Attribute not found!");
		return null;
	}
}
