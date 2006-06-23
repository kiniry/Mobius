/*
 * Created on 2005-05-13
 *
 */
package umbra;


/**
 * The interface defining colors used in particular coloring styles
 * 
 * @author Wojtek W�s
 */
public interface IColorValues {
    /**
     * TODO write description
     */
    static int PARTS = 16;
    /**
     * TODO write description
     */
    static int STRING = 0;
    /**
     * TODO write description
     */
    static int COMMENT = 1;
    /**
     * TODO write description
     */
    static int DEFAULT = 2;
    /**
     * TODO write description
     */
    static int ERROR = 3;
    /**
     * TODO write description
     */
    static int HEADER = 4;
    /**
     * TODO write description
     */
    static int TAG = 5;
    /**
     * TODO write description
     */
    static int CLASS = 6;
    /**
     * TODO write description
     */
    static int BTC_INSTR = 7;
    /**
     * TODO write description
     */
    static int KEY = 8;
    /**
     * TODO write description
     */
    static int LINE = 9;
    /**
     * TODO write description
     */
    static int THROWS = 10;
    /**
     * TODO write description
     */
    static int SQUARE = 11;
    /**
     * TODO write description
     */
    static int NUMBER = 12;
	/**
     * TODO write description
     */
    static int POSITION = 13;
    /**
     * TODO write description
     */
    static int HASH = 14;
    /**
     * TODO write description
     */
    static int ATTR = 15;
	
    /**
     * TODO write description
     */
    static int[][] models = new int[][] {new int[] {0, 0, 255, 0,
		0, 0, 0, 2, 0, 0, 0, 0, 255, 0, 0, 0, 
		0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 
		0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
		0, 0, 0, 2, 0, 0, 0, 2},
		new int[] {0, 255, 0, 0, 
		128, 128, 128, 2, 0, 0, 0, 0, 255, 0, 0, 0, 
		0, 0, 0, 1, 0, 0, 128, 0, 0, 0, 128, 0, 
		255, 160, 0, 3, 0, 0, 255, 1, 0, 192, 128, 0, 0, 192, 128, 0,
		0, 128, 64, 0, 255, 224, 0, 1, 255, 224, 0, 1,
		224, 255, 0, 3, 224, 0, 255, 3},
		new int[] {0, 0, 255, 0, 
		255, 128, 255, 2, 64, 0, 64, 0, 255, 64, 0, 1, 
		192, 0, 192, 1, 128, 0, 128, 0, 128, 0, 128, 0, 
		128, 0, 255, 1, 128, 0, 128, 0, 128, 0, 192, 0,  192, 0, 192, 0, 
		192, 0, 192, 0, 128, 0, 128, 1, 128, 0, 128, 1, 
		255, 0, 255, 1, 255, 0, 255, 1},
		new int[] {128, 128, 0, 0, 
		192, 192, 192, 0, 128, 128, 128, 0, 255, 0, 0, 1, 
		64, 64, 64, 1, 128, 128, 128, 0, 128, 128, 128, 0,  
		64, 64, 64, 1, 128, 128, 128, 1, 128, 128, 128, 1, 64, 64, 64, 1,  
		255, 192, 128, 1, 0, 192, 0, 1, 0, 192, 0, 1, 
		192, 192, 0, 1, 192, 192, 0, 1},
		new int[] {0, 255, 255, 0, 
		128, 128, 128, 0, 0, 0, 0, 0, 255, 0, 0, 2, 
		0, 0, 0, 0, 0, 128, 128, 0, 0, 128, 128, 0, 
		0, 128, 128, 0, 0, 128, 128, 0, 0, 0, 0, 0, 0, 0, 0, 0,  
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
		0, 0, 0, 0, 0, 0, 0, 0},
		new int[] {0, 0, 255, 0,
		0, 128, 0, 0, 0, 0, 0, 0, 255, 0, 0, 0, 
		128, 0, 64, 1, 0, 64, 128, 0, 0, 64, 128, 0, 
		64, 0, 64, 1, 64, 0, 64, 1, 128, 0, 128, 0, 128, 0, 64, 1, 
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 
		0, 0, 0, 0, 0, 0, 0, 0},
		new int[] {64, 255, 96, 0,
		160, 0, 128, 1, 192, 64, 255, 2, 96, 160, 0, 3,
		128, 192, 64, 0, 255, 96, 160, 1, 0, 128, 192, 2,
		192, 128, 0, 3, 160, 96, 255, 0, 64, 192, 128, 1,
		0, 160, 96, 2, 255, 64, 192, 3, 128, 0, 160, 0,
		96, 255, 64, 1, 64, 255, 96, 2, 160, 0, 128, 3},
		new int[] {128, 128, 128, 0,
		128, 128, 128, 0, 128, 128, 128, 0, 128, 128, 128, 0,
		128, 128, 128, 0, 128, 128, 128, 0, 128, 128, 128, 0,
		128, 128, 128, 0, 128, 128, 128, 0, 128, 128, 128, 0,
		128, 128, 128, 0, 128, 128, 128, 0, 128, 128, 128, 0,
		128, 128, 128, 0, 128, 128, 128, 0, 128, 128, 128, 0}
	};
		
}
