package annot.bcclass;

@Deprecated
public class OldPrittyPrinter implements IPrittyPrinter {

	private BMLConfig conf;
	
	public OldPrittyPrinter(BMLConfig conf) {
		this.conf = conf;
	}

	public String afterDisplay(String str) {
		return str;
	}
	
	// debug array print, will be removed shortly
	private void printArr(int[] arr, int cnt) {
		for (int i=0; i<cnt; i++)
			System.out.print(arr[i]);
		System.out.println();
	}

	/**
	 * Line-breaking for expression str. Characters
	 * conf.expr_block_start and conf.expr_block_end
	 * represents blocks boundaries.
	 * 
	 * @param conf - see {@link BMLConfig}
	 * @param str - expression to be divided
	 * @param spos - current position in line
	 * @return str with conf.newLine()'s
	 * 			and without block boundaries
	 */
	public String breakLines(String str, int spos) {
		boolean debug = false;
		int strlen = str.length();
		int maxlen = conf.max_line_width;
		int pos = 0;
		int d = 0;
		int charc = 0;
		String line = "";
		int[] depth = new int[strlen];
		while (pos < strlen) {
			char ch = str.charAt(pos);
			if (ch == '{') {
				d++;
			} else if (ch == '}') {
				d--;
			} else {
				depth[charc] = d;
				line += ch;
				charc++;
			}
			pos++;
		}
		int maxl = maxlen - spos;
		if (charc <= maxl)
			return line;
		if (debug) {
			for (int i=0; i<10; i++)
				System.out.print("V---------");
			System.out.println("/n  charc="+charc+", maxl="+maxl);
			System.out.println(str);
			System.out.println(line);
			printArr(depth, charc);
		}
		double[] bonus = new double[256];
		for (int i=0; i<256; i++)
			bonus[i] = 1;
		bonus[(int)'['] = 0.5;
		bonus[(int)'.'] = 0.3;
		int startp = 0;
		String res = "";
		while (true) {
			int endp = startp + maxl;
			if (debug)
				System.out.println(line.substring(startp, endp));
			boolean[] ok = new boolean[maxl];
			for (int i=0; i<maxl; i++)
				ok[i] = false;
			int[] br = new int[maxl];
			int brc = 0;
			int lastd = 1000;
			for (int i=endp-1; i>startp; i--) {
				if ((depth[i] < depth[i-1]) && (depth[i] < lastd)) {
					int j = i-1;
					char ch;
					do {
						j++;
						ch = line.charAt(j);
					} while ((j < endp) && ((ch == ')') || (ch == ']') || (ch == ';')));
					if (j < endp) {
						ok[j-startp] = true;
						lastd = depth[i];
						br[brc++] = j;
					}
				}
			}
			br[brc] = startp;
			if (debug) {
				for (int i=0; i<maxl; i++)
					System.out.print(ok[i] ? "X" : ".");
				System.out.println();
			}
			int npos = startp + maxl;
			if (brc > 0) {
				int bestp = 0;
				double bestv = 1000 * ((double)(br[0] - br[1]) / (endp - br[1])) - Math.pow(endp - br[0], 2);
				bestv *= bonus[(int)(line.charAt(br[0]))];
				if (debug)
					System.out.print((int)bestv);
				for (int i=1; i<brc; i++) {
					double v = -1;
					if (br[i-1] > br[i])
						v = 2000 * ((double)(br[i] - br[i+1]) / (br[i-1] - br[i+1])) - Math.pow(endp - br[i], 2);
					v *= bonus[(int)(line.charAt(br[i]))];
					if (debug)
						System.out.print("  " + (int)v);
					if (v > bestv) {
						bestv = v;
						bestp = i;
					}
				}
				npos = br[bestp];
				if (debug) {
					System.out.println();
					for (int i=0; i<maxl; i++)
						System.out.print(i+startp == br[bestp] ? "#" : ".");
					System.out.println();
				}
			}
			res += line.substring(startp, npos) + conf.newLine();
			if (npos + maxlen >= charc) {
				res += line.substring(npos);
				break;
			}
			maxl = maxlen;
			startp = npos;
			if (debug)
				System.out.println("+++++++++++++");
		}
		return res;
	}
}
