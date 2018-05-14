import java.util.concurrent.*;
import java.util.concurrent.locks.*;

/*@ 
    predicate_ctor BCounter_shared_state (BCounter c) () =
        c.N |-> ?v &*& v >= 0 &*& c.MAX |-> ?m &*& m > 0 &*& v <= m;
@*/

/*@ predicate BCounterInv(BCounter c) = 
    c.mon |-> ?l &*&
    l != null &*& lck(l,1,BCounter_shared_state(c));
@*/

class BCounter {
  int N;
  int MAX;
  ReentrantLock mon;

  BCounter(int max)
  //@ requires 0 < max;
  //@ ensures BCounterInv(this);
  { 
      N = 0 ; 
      MAX = max; 
      //@ close BCounter_shared_state(this)();
      //@ close enter_lck(1,BCounter_shared_state(this));
      mon = new ReentrantLock(); 
      //@ close BCounterInv(this);
  }

  void inc()
  //@ requires BCounterInv(this);
  //@ ensures BCounterInv(this);
  { 
      //@ open BCounterInv(this);
      mon.lock(); // request permission to the shared state
      //@ open BCounter_shared_state(this)();
      if ( N < MAX ) N++;
      //@ close BCounter_shared_state(this)();
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
      if ( N > 0 ) N--; 
      //@ close BCounter_shared_state(this)();
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