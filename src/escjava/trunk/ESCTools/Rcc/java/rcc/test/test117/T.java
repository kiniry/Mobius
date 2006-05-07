


class T {
    int x;
    void f() {
        T.this.x = 2;
        this.x = 3;
    }
}
