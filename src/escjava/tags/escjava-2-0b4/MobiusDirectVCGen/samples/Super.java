public class Super {

	Super i;
	int j, k;
	
	//@requires i != null;
	//@ensures \result == this;
	//@assignable \everything;
	public Super f(Super i){
		
		//@assert true;
		//@assume false;
		int noghosti = 0;
		//@ghost int ghosti = 3;
		noghosti = 1;
		//@set ghosti = 5;
		//@maintaining noghosti >= 0;
		while (noghosti <10){
			noghosti++;
		}
		return i;
	}	
}