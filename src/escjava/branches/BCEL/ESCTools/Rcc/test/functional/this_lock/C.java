class C {
  Object f /*#guarded_by this*/;
  synchronized void ma() {
    f = null;
  }
  void mb() {
    synchronized (this) {
      f = null;
    }
  }
}
