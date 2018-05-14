import java.util.concurrent.*;
import java.util.concurrent.locks.*;

/*@

predicate_ctor BCounter_shared_state (BCounter c) () =
   c.N |-> ?v &*& v >= 0 &*& c.MAX |-> ?m &*& m > 0 &*& v <= m;

predicate_ctor BCounter_nonzero (BCounter c) () =
   c.N |-> ?v &*& c.MAX |-> ?m &*& v > 0 &*& m > 0 &*& v <= m; 

predicate_ctor BCounter_nonmax (BCounter c) () =
   c.N |-> ?v &*& c.MAX |-> ?m &*& v < m &*& m > 0 &*& v >= 0; 

predicate BCounterInv(BCounter c) = 
        c.mon |-> ?l 
    &*& l != null 
    &*& lck(l,1, BCounter_shared_state(c)) 
    &*& c.notzero |-> ?cc 
    &*& cc !=null 
    &*& cond(cc, BCounter_shared_state(c), BCounter_nonzero(c))
    &*& c.notmax |-> ?cm 
    &*& cm !=null 
    &*& cond(cm, BCounter_shared_state(c), BCounter_nonmax(c));
@*/


class BCounter {
  int N;
  int MAX;
  ReentrantLock mon;
  Condition notzero;
  Condition notmax;

  BCounter(int max)
  //@ requires 0 < max;
  //@ ensures BCounterInv(this);
  { 
      N = 0 ; 
      MAX = max; 
      //@ close BCounter_shared_state(this)();
      //@ close enter_lck(1,BCounter_shared_state(this));
      mon = new ReentrantLock(); 
      //@ close set_cond(BCounter_shared_state(this),BCounter_nonzero(this));
      notzero = mon.newCondition();
      //@ close set_cond(BCounter_shared_state(this),BCounter_nonmax(this));
      notmax = mon.newCondition();
      //@ close BCounterInv(this);
  }

  void inc()
  //@ requires BCounterInv(this);
  //@ ensures BCounterInv(this);
  { 
      //@ open BCounterInv(this);
      // request permission to enter the monitor and access 
      // the conditions and the values of the fields N and MAX.
      mon.lock();
      //@ open BCounter_shared_state(this)();
      // Wait for the preconditions of the operations to hold.
      // Wait until the condition is met or another thread releases 
      // the monitor in a compatible state.
      
  
	//if( N == MAX ){
	//	//@ close BCounter_shared_state(this)();
	//	notmax.wait();
	//	//@ open BCounter_nonmax(this)();
	//}
      
     // But we need a loop to avoid spurious wakeps
      while ( N == MAX ) 
      /*@ invariant this.N |-> ?v 
      	          &*& v >= 0 
      	          &*& this.MAX |-> ?m 
      	          &*& m > 0 
      	          &*& v <= m 
      	          &*& this.notzero |-> ?cc 
      	          &*& cc !=null 
      	          &*& cond(cc, BCounter_shared_state(this), BCounter_nonzero(this)) 
      	          &*& this.notmax |-> ?cm
      	          &*& cm !=null 
      	          &*& cond(cm, BCounter_shared_state(this), BCounter_nonmax(this));
      @*/
      { // The invariant is necessary to propagate the knowledge
        //@ close BCounter_shared_state(this)(); 
	notmax.await();
      	//@ open BCounter_nonmax(this)(); 
      }

      N++;
      //@ close BCounter_nonzero(this)();
      notzero.signal();
      mon.unlock(); // release ownership of the shared state
      //@ close BCounterInv(this);
  } 

  void dec()
  //@ requires BCounterInv(this);
  //@ ensures BCounterInv(this);
  { 
      //@ open BCounterInv(this);
      mon.lock(); // request permission to the shared state
      //@ open BCounter_shared_state(this)();
      while ( N == 0 )
      	/*@ invariant this.N |-> ?v 
      	          &*& v >= 0 
      	          &*& this.MAX |-> ?m 
      	          &*& m > 0 
      	          &*& v <= m 
      	          &*& this.notzero |-> ?cc 
      	          &*& cc !=null 
      	          &*& cond(cc, BCounter_shared_state(this), BCounter_nonzero(this)) 
      	          &*& this.notmax |-> ?cm
      	          &*& cm !=null 
      	          &*& cond(cm, BCounter_shared_state(this), BCounter_nonmax(this)); 
      	@*/
      {
        //@ close BCounter_shared_state(this)(); 
      	notzero.await();
      	//@ open BCounter_nonzero(this)(); 
      }
      //@ assert N > 0;

      N--; 
      //@ assert N < MAX;
      //@ close BCounter_nonmax(this)(); 
      notmax.signal();
      mon.unlock(); // release ownership of the shared state
      //@ close BCounterInv(this);
  } 
  
  int get()
  //@ requires BCounterInv(this);
  //@ ensures BCounterInv(this);
  { 
      int r;
      //@ open BCounterInv(this);
      mon.lock(); 
      //@ open BCounter_shared_state(this)();
      r = N; // put a copy on the stack, private to the thread
      //@ close BCounter_shared_state(this)();
      mon.unlock();	
      //@ close BCounterInv(this);
      return r;
  } 

  public static void main(String[] args) 
  //@ requires true;
  //@ ensures true;
  {
       int MAX = 100;
       BCounter c = new BCounter(MAX);
       //@ assert BCounterInv(c);
       c.inc();         
  }
}