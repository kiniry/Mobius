package java.util.concurrent;

class ExecutorCompletionService$QueueingFuture extends FutureTask {
    /*synthetic*/ final ExecutorCompletionService this$0;
    
    ExecutorCompletionService$QueueingFuture(/*synthetic*/ final ExecutorCompletionService this$0, Callable c) {
        super( this.this$0 = c);
    }
    
    ExecutorCompletionService$QueueingFuture(/*synthetic*/ final ExecutorCompletionService this$0, Runnable t, Object r) {
        super(t, r);
	 this.this$0 = this$0;

    }
    
    protected void done() {
        ExecutorCompletionService.access$000(this$0).add(this);
    }
}
