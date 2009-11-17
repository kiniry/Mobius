package java.net;

import java.lang.Character;

class URI$Parser {
    /*synthetic*/ final URI this$0;
    private String input;
    private boolean requireServerAuthority = false;
    
    URI$Parser(/*synthetic*/ final URI this$0, String s) {
        this.this$0 = this$0;
        
        input = s;
        URI.access$002(this$0, s);
    }
    
    private void fail(String reason) throws URISyntaxException {
        throw new URISyntaxException(input, reason);
    }
    
    private void fail(String reason, int p) throws URISyntaxException {
        throw new URISyntaxException(input, reason, p);
    }
    
    private void failExpecting(String expected, int p) throws URISyntaxException {
        fail("Expected " + expected, p);
    }
    
    private void failExpecting(String expected, String prior, int p) throws URISyntaxException {
        fail("Expected " + expected + " following " + prior, p);
    }
    
    private String substring(int start, int end) {
        return input.substring(start, end);
    }
    
    private char charAt(int p) {
        return input.charAt(p);
    }
    
    private boolean at(int start, int end, char c) {
        return (start < end) && (charAt(start) == c);
    }
    
    private boolean at(int start, int end, String s) {
        int p = start;
        int sn = s.length();
        if (sn > end - p) return false;
        int i = 0;
        while (i < sn) {
            if (charAt(p++) != s.charAt(i)) {
                break;
            }
            i++;
        }
        return (i == sn);
    }
    
    private int scan(int start, int end, char c) {
        if ((start < end) && (charAt(start) == c)) return start + 1;
        return start;
    }
    
    private int scan(int start, int end, String err, String stop) {
        int p = start;
        while (p < end) {
            char c = charAt(p);
            if (err.indexOf(c) >= 0) return -1;
            if (stop.indexOf(c) >= 0) break;
            p++;
        }
        return p;
    }
    
    private int scanEscape(int start, int n, char first) throws URISyntaxException {
        int p = start;
        char c = first;
        if (c == '%') {
            if ((p + 3 <= n) && URI.access$300(charAt(p + 1), URI.access$100(), URI.access$200()) && URI.access$300(charAt(p + 2), URI.access$100(), URI.access$200())) {
                return p + 3;
            }
            fail("Malformed escape pair", p);
        } else if ((c > 128) && !Character.isSpaceChar(c) && !Character.isISOControl(c)) {
            return p + 1;
        }
        return p;
    }
    
    private int scan(int start, int n, long lowMask, long highMask) throws URISyntaxException {
        int p = start;
        while (p < n) {
            char c = charAt(p);
            if (URI.access$300(c, lowMask, highMask)) {
                p++;
                continue;
            }
            if ((lowMask & 1L) != 0) {
                int q = scanEscape(p, n, c);
                if (q > p) {
                    p = q;
                    continue;
                }
            }
            break;
        }
        return p;
    }
    
    private void checkChars(int start, int end, long lowMask, long highMask, String what) throws URISyntaxException {
        int p = scan(start, end, lowMask, highMask);
        if (p < end) fail("Illegal character in " + what, p);
    }
    
    private void checkChar(int p, long lowMask, long highMask, String what) throws URISyntaxException {
        checkChars(p, p + 1, lowMask, highMask, what);
    }
    
    void parse(boolean rsa) throws URISyntaxException {
        requireServerAuthority = rsa;
        int ssp;
        int n = input.length();
        int p = scan(0, n, "/?#", ":");
        if ((p >= 0) && at(p, n, ':')) {
            if (p == 0) failExpecting("scheme name", 0);
            checkChar(0, 0L, URI.access$400(), "scheme name");
            checkChars(1, p, URI.access$500(), URI.access$600(), "scheme name");
            URI.access$702(this$0, substring(0, p));
            p++;
            ssp = p;
            if (at(p, n, '/')) {
                p = parseHierarchical(p, n);
            } else {
                int q = scan(p, n, "", "#");
                if (q <= p) failExpecting("scheme-specific part", p);
                checkChars(p, q, URI.access$800(), URI.access$900(), "opaque part");
                p = q;
            }
        } else {
            ssp = 0;
            p = parseHierarchical(0, n);
        }
        URI.access$1002(this$0, substring(ssp, p));
        if (at(p, n, '#')) {
            checkChars(p + 1, n, URI.access$800(), URI.access$900(), "fragment");
            URI.access$1102(this$0, substring(p + 1, n));
            p = n;
        }
        if (p < n) fail("end of URI", p);
    }
    
    private int parseHierarchical(int start, int n) throws URISyntaxException {
        int p = start;
        if (at(p, n, '/') && at(p + 1, n, '/')) {
            p += 2;
            int q = scan(p, n, "", "/?#");
            if (q > p) {
                p = parseAuthority(p, q);
            } else if (q < n) {
            } else failExpecting("authority", p);
        }
        int q = scan(p, n, "", "?#");
        checkChars(p, q, URI.access$1200(), URI.access$1300(), "path");
        URI.access$1402(this$0, substring(p, q));
        p = q;
        if (at(p, n, '?')) {
            p++;
            q = scan(p, n, "", "#");
            checkChars(p, q, URI.access$800(), URI.access$900(), "query");
            URI.access$1502(this$0, substring(p, q));
            p = q;
        }
        return p;
    }
    
    private int parseAuthority(int start, int n) throws URISyntaxException {
        int p = start;
        int q = p;
        URISyntaxException ex = null;
        boolean serverChars;
        boolean regChars;
        if (scan(p, n, "", "]") > p) {
            serverChars = (scan(p, n, URI.access$1600(), URI.access$1700()) == n);
        } else {
            serverChars = (scan(p, n, URI.access$1800(), URI.access$1900()) == n);
        }
        regChars = (scan(p, n, URI.access$2000(), URI.access$2100()) == n);
        if (regChars && !serverChars) {
            URI.access$2202(this$0, substring(p, n));
            return n;
        }
        if (serverChars) {
            try {
                q = parseServer(p, n);
                if (q < n) failExpecting("end of authority", q);
                URI.access$2202(this$0, substring(p, n));
            } catch (URISyntaxException x) {
                URI.access$2302(this$0, null);
                URI.access$2402(this$0, null);
                URI.access$2502(this$0, -1);
                if (requireServerAuthority) {
                    throw x;
                } else {
                    ex = x;
                    q = p;
                }
            }
        }
        if (q < n) {
            if (regChars) {
                URI.access$2202(this$0, substring(p, n));
            } else if (ex != null) {
                throw ex;
            } else {
                fail("Illegal character in authority", q);
            }
        }
        return n;
    }
    
    private int parseServer(int start, int n) throws URISyntaxException {
        int p = start;
        int q;
        q = scan(p, n, "/?#", "@");
        if ((q >= p) && at(q, n, '@')) {
            checkChars(p, q, URI.access$2600(), URI.access$2700(), "user info");
            URI.access$2302(this$0, substring(p, q));
            p = q + 1;
        }
        if (at(p, n, '[')) {
            p++;
            q = scan(p, n, "/?#", "]");
            if ((q > p) && at(q, n, ']')) {
                int r = scan(p, q, "", "%");
                if (r > p) {
                    parseIPv6Reference(p, r);
                    if (r + 1 == q) {
                        fail("scope id expected");
                    }
                    checkChars(r + 1, q, URI.access$2800(), URI.access$2900(), "scope id");
                } else {
                    parseIPv6Reference(p, q);
                }
                URI.access$2402(this$0, substring(p - 1, q + 1));
                p = q + 1;
            } else {
                failExpecting("closing bracket for IPv6 address", q);
            }
        } else {
            q = parseIPv4Address(p, n);
            if (q <= p) q = parseHostname(p, n);
            p = q;
        }
        if (at(p, n, ':')) {
            p++;
            q = scan(p, n, "", "/");
            if (q > p) {
                checkChars(p, q, URI.access$3000(), 0L, "port number");
                try {
                    URI.access$2502(this$0, Integer.parseInt(substring(p, q)));
                } catch (NumberFormatException x) {
                    fail("Malformed port number", p);
                }
                p = q;
            }
        }
        if (p < n) failExpecting("port number", p);
        return p;
    }
    
    private int scanByte(int start, int n) throws URISyntaxException {
        int p = start;
        int q = scan(p, n, URI.access$3000(), 0L);
        if (q <= p) return q;
        if (Integer.parseInt(substring(p, q)) > 255) return p;
        return q;
    }
    
    private int scanIPv4Address(int start, int n, boolean strict) throws URISyntaxException {
        int p = start;
        int q;
        int m = scan(p, n, URI.access$3000() | URI.access$3100(), 0L | URI.access$3200());
        if ((m <= p) || (strict && (m != n))) return -1;
        for (; ; ) {
            if ((q = scanByte(p, m)) <= p) break;
            p = q;
            if ((q = scan(p, m, '.')) <= p) break;
            p = q;
            if ((q = scanByte(p, m)) <= p) break;
            p = q;
            if ((q = scan(p, m, '.')) <= p) break;
            p = q;
            if ((q = scanByte(p, m)) <= p) break;
            p = q;
            if ((q = scan(p, m, '.')) <= p) break;
            p = q;
            if ((q = scanByte(p, m)) <= p) break;
            p = q;
            if (q < m) break;
            return q;
        }
        fail("Malformed IPv4 address", q);
        return -1;
    }
    
    private int takeIPv4Address(int start, int n, String expected) throws URISyntaxException {
        int p = scanIPv4Address(start, n, true);
        if (p <= start) failExpecting(expected, start);
        return p;
    }
    
    private int parseIPv4Address(int start, int n) {
        int p;
        try {
            p = scanIPv4Address(start, n, false);
        } catch (URISyntaxException x) {
            return -1;
        } catch (NumberFormatException nfe) {
            return -1;
        }
        if (p > start && p < n) {
            if (charAt(p) != ':') {
                p = -1;
            }
        }
        if (p > start) URI.access$2402(this$0, substring(start, p));
        return p;
    }
    
    private int parseHostname(int start, int n) throws URISyntaxException {
        int p = start;
        int q;
        int l = -1;
        do {
            q = scan(p, n, URI.access$2800(), URI.access$2900());
            if (q <= p) break;
            l = p;
            if (q > p) {
                p = q;
                q = scan(p, n, URI.access$2800() | URI.access$3300(), URI.access$2900() | URI.access$3400());
                if (q > p) {
                    if (charAt(q - 1) == '-') fail("Illegal character in hostname", q - 1);
                    p = q;
                }
            }
            q = scan(p, n, '.');
            if (q <= p) break;
            p = q;
        }         while (p < n);
        if ((p < n) && !at(p, n, ':')) fail("Illegal character in hostname", p);
        if (l < 0) failExpecting("hostname", start);
        if (l > start && !URI.access$300(charAt(l), 0L, URI.access$400())) {
            fail("Illegal character in hostname", l);
        }
        URI.access$2402(this$0, substring(start, p));
        return p;
    }
    private int ipv6byteCount = 0;
    
    private int parseIPv6Reference(int start, int n) throws URISyntaxException {
        int p = start;
        int q;
        boolean compressedZeros = false;
        q = scanHexSeq(p, n);
        if (q > p) {
            p = q;
            if (at(p, n, "::")) {
                compressedZeros = true;
                p = scanHexPost(p + 2, n);
            } else if (at(p, n, ':')) {
                p = takeIPv4Address(p + 1, n, "IPv4 address");
                ipv6byteCount += 4;
            }
        } else if (at(p, n, "::")) {
            compressedZeros = true;
            p = scanHexPost(p + 2, n);
        }
        if (p < n) fail("Malformed IPv6 address", start);
        if (ipv6byteCount > 16) fail("IPv6 address too long", start);
        if (!compressedZeros && ipv6byteCount < 16) fail("IPv6 address too short", start);
        if (compressedZeros && ipv6byteCount == 16) fail("Malformed IPv6 address", start);
        return p;
    }
    
    private int scanHexPost(int start, int n) throws URISyntaxException {
        int p = start;
        int q;
        if (p == n) return p;
        q = scanHexSeq(p, n);
        if (q > p) {
            p = q;
            if (at(p, n, ':')) {
                p++;
                p = takeIPv4Address(p, n, "hex digits or IPv4 address");
                ipv6byteCount += 4;
            }
        } else {
            p = takeIPv4Address(p, n, "hex digits or IPv4 address");
            ipv6byteCount += 4;
        }
        return p;
    }
    
    private int scanHexSeq(int start, int n) throws URISyntaxException {
        int p = start;
        int q;
        q = scan(p, n, URI.access$100(), URI.access$200());
        if (q <= p) return -1;
        if (at(q, n, '.')) return -1;
        if (q > p + 4) fail("IPv6 hexadecimal digit sequence too long", p);
        ipv6byteCount += 2;
        p = q;
        while (p < n) {
            if (!at(p, n, ':')) break;
            if (at(p + 1, n, ':')) break;
            p++;
            q = scan(p, n, URI.access$100(), URI.access$200());
            if (q <= p) failExpecting("digits for an IPv6 address", p);
            if (at(q, n, '.')) {
                p--;
                break;
            }
            if (q > p + 4) fail("IPv6 hexadecimal digit sequence too long", p);
            ipv6byteCount += 2;
            p = q;
        }
        return p;
    }
}
