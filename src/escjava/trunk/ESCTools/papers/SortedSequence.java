public class SortedSequence  {

	private /*@ spec_public */ int[] seq = new int[9];
	private /*@ spec_public */ int size = 0;
	//@ invariant seq != null;
	//@ invariant size >= 0 && size <= seq.length;

	//@ requires true;
	//@ assignable seq, seq[*];
	public void push(int i) {
	    if (size == seq.length) {
	        int[] newseq = new int[2 * seq.length];
	        System.arraycopy(seq,0,newseq,0,size);
	        seq = newseq;
	    }
	    seq[size++] = i;
	}

	//@ requires size > 0;
	//@ assignable seq[*];
	//@ ensures \result == sort()[size-1];
	public int pop() {
	    seq = sort();
	    return seq[--size];
	}

	//@ pure
	private int[] sort() { ... }

}
