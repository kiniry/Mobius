/**
 * TODO licence
 */
package escjava.extensions.universes;

import escjava.extensions.IESCInitComponentView;

/**
 * This class implements the initialisation of the
 * Universe type system extension. 
 * 
 * @author Aleksy Schubert
 *
 */
public class InitUniverses implements IESCInitComponentView {

	/**
	 * This field caches the only ESC Universes init
	 * object.
	 */
	static private InitUniverses currentInit;
	
	/**
	 * The field which says if the universe types should be recognized 
	 * and checked.
	 */
	private boolean useUniverseTypeSystem = false;
	
	/**
	 * The location of the universe type system modifiers:
	 * <ul>
	 * <li>	modifiers in comments => mod 2 == 0
	 * <li> modifiers as keyword  => mod 3 == 0
	 * <li> no checking           => mod 5 == 0  
	 * </ul>
	 * Initially it contains a value which is relatively prime to
	 * all the moduli above.
	 */
	private int universeLevel = 23;
	
	/**
	 * The actual initialisation is done at the
	 * Javafe level so we store here a link to
	 * the initialisation object there.
	 */
	javafe.extensions.universes.InitUniverses currentJavafeInit;
	
	/**
	 * This constructor does nothing.
	 */
	public InitUniverses() {
		if (currentInit!=null) {
			throw new RuntimeException("Only one ESC Universes init object is allowed to exist");
		}
		currentInit = this;
	}
	
	/**
	 * The method returns an internally cached reference
	 * to the Javafe Universes extension where all the
	 * initialisation parameters are stored. The method
	 * checks if the reference is non-null and in case
	 * it is null it attempts to fetch the reference
	 * from the Javafe Universe component. 
	 * 
	 * @return the internal representation of the Javafe
	 *         extension
	 */
	private javafe.extensions.universes.InitUniverses getJavafeInit() {
		if (currentJavafeInit==null) {
			currentJavafeInit = javafe.extensions.universes.InitUniverses.getCurrentInit(); 
		}
		return currentJavafeInit;
	}
	
	/**
	 * The method gives the current value of the universe
	 * type system level. It tries to get the information
	 * from Javafe init, and if fails it returns the local
	 * default values.
	 * 
	 * @return the universe level value
	 */
	public int getUniverseLevel() {
		javafe.extensions.universes.InitUniverses ji = javafe.extensions.universes.InitUniverses.getCurrentInit();
		if (ji==null) {
			return universeLevel;
		} else {
			return ji.getUniverseLevel();
		}
	}

	/**
	 * The method returns true when the universe
	 * type system is to be used. It tries to get the information
	 * from Javafe init, and if fails it returns the local
	 * default values.
	 * 
	 * @return the universe level value
	 */
	public boolean getUseUniverseTypeSystem() {
		javafe.extensions.universes.InitUniverses ji = javafe.extensions.universes.InitUniverses.getCurrentInit();
		if (ji==null) {
			return useUniverseTypeSystem;
		} else {
			return ji.getUseUniverseTypeSystem();
		}		
	}

	/**
	 * This method currently does nothing as all the options
	 * are set in Javafe.
	 * 
	 * @see escjava.extensions.IESCInitComponentView#processOption(String option, String[] args, int offset)
	 */
	public int processOption(String option, String[] args, int offset) {
		return offset;
	}
	
}
