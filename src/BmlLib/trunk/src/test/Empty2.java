package test;

public class Empty2 {

	static int l = 0;

	private static int fib(int n) {
		l++;
		if (n < 2)
			return n;
		int[] last = new int[3];
		last[0] = 0;
		last[1] = 1;
		for (int i = 2; i <= n; i++)
			last[i % 3] = last[(i - 1) % 3] + last[(i - 2) % 3];
		return last[n % 3];
	}

	public static void main(String[] args) {
		int x = fib(1);
		int y = fib(6);
		int z = fib(Empty.c);
		int d = x + y + z;
		System.out.println("n=" + d + ", l=" + l);
	}

}
