/*
Solution for Fractional Permissions for Concurrent Counter, Lab 8
CVS course - Integrated Master in Computer Science and Engineering
@FCT UNL João Costa Seco 2018
*/

import java.util.concurrent.*;
import java.util.concurrent.locks.*;

/*@

predicate_ctor CCounter_shared_state (CCounter c) () =
   c.N |-> ?v &*& v >= 0 &*& c.MAX |-> ?m &*& m > 0 &*& v <= m;

predicate_ctor CCounter_nonzero (CCounter c) () =
   c.N |-> ?v &*& c.MAX |-> ?m &*& v > 0 &*& m > 0 &*& v <= m; 

predicate_ctor CCounter_nonmax (CCounter c) () =
   c.N |-> ?v &*& c.MAX |-> ?m &*& v < m &*& m > 0 &*& v >= 0; 

predicate CCounterInv(CCounter c;) = 
        c.mon |-> ?l 
    &*& l != null 
    &*& lck(l,1, CCounter_shared_state(c)) 
    &*& c.notzero |-> ?cc 
    &*& cc !=null 
    &*& cond(cc, CCounter_shared_state(c), CCounter_nonzero(c))
    &*& c.notmax |-> ?cm 
    &*& cm !=null 
    &*& cond(cm, CCounter_shared_state(c), CCounter_nonmax(c));
@*/


class CCounter {
  int N;
  int MAX;
  ReentrantLock mon;
  Condition notzero;
  Condition notmax;

  CCounter(int max)
  //@ requires 0 < max;
  //@ ensures CCounterInv(this);
  { 
      N = 0 ; 
      MAX = max; 
      //@ close CCounter_shared_state(this)();
      //@ close enter_lck(1,CCounter_shared_state(this));
      mon = new ReentrantLock(); 
      //@ close set_cond(CCounter_shared_state(this),CCounter_nonzero(this));
      notzero = mon.newCondition();
      //@ close set_cond(CCounter_shared_state(this),CCounter_nonmax(this));
      notmax = mon.newCondition();
      //@ close CCounterInv(this);
  }

  void inc()
  //@ requires [?f]CCounterInv(this);
  //@ ensures [f]CCounterInv(this);
  { 
      //@ open CCounterInv(this);
      // request permission to enter the monitor and access 
      // the conditions and the values of the fields N and MAX.
      mon.lock();
      //@ open CCounter_shared_state(this)();
      // Wait for the preconditions of the operations to hold.
      // Wait until the condition is met or another thread releases 
      // the monitor in a compatible state.
      
      // if( N == MAX ) notmax.wait(); 
      
      // But we need a loop to avoid spurious wakeps
      while ( N == MAX ) 
      /*@ invariant this.N |-> ?v 
      	          &*& v >= 0 
      	          &*& this.MAX |-> ?m 
      	          &*& m > 0 
      	          &*& v <= m 
      	          &*& [f]this.notzero |-> ?cc 
      	          &*& cc !=null 
      	          &*& [f]cond(cc, CCounter_shared_state(this), CCounter_nonzero(this)) 
      	          &*& [f]this.notmax |-> ?cm
      	          &*& cm !=null 
      	          &*& [f]cond(cm, CCounter_shared_state(this), CCounter_nonmax(this));
      @*/
      { // The invariant is necessary to propagate the knowledge
        //@ close CCounter_shared_state(this)(); 
	       notmax.await();
      	//@ open CCounter_nonmax(this)(); 
      }
      N++;
      //@ close CCounter_nonzero(this)();
      notzero.signal();
      mon.unlock(); // release ownership of the shared state
      //@ close [f]CCounterInv(this);
  } 

  void dec()
  //@ requires [?f]CCounterInv(this);
  //@ ensures [f]CCounterInv(this);
  { 
      //@ open CCounterInv(this);
      mon.lock(); // request permission to the shared state
      //@ open CCounter_shared_state(this)();
      while ( N == 0 )
      	/*@ invariant this.N |-> ?v 
      	          &*& v >= 0 
      	          &*& this.MAX |-> ?m 
      	          &*& m > 0 
      	          &*& v <= m 
      	          &*& [f]this.notzero |-> ?cc 
      	          &*& cc !=null 
      	          &*& [f]cond(cc, CCounter_shared_state(this), CCounter_nonzero(this)) 
      	          &*& [f]this.notmax |-> ?cm
      	          &*& cm !=null 
      	          &*& [f]cond(cm, CCounter_shared_state(this), CCounter_nonmax(this)); 
      	@*/
      {
        //@ close CCounter_shared_state(this)(); 
      	notzero.await();
      	//@ open CCounter_nonzero(this)(); 
      }
      //@ assert N > 0;

      N--; 
      //@ assert N < MAX;
      //@ close CCounter_nonmax(this)(); 
      notmax.signal();
      mon.unlock(); // release ownership of the shared state
      //@ close [f]CCounterInv(this);
  } 
  
  int get()
  //@ requires CCounterInv(this);
  //@ ensures CCounterInv(this);
  { 
      int r;
      //@ open CCounterInv(this);
      mon.lock(); 
      //@ open CCounter_shared_state(this)();
      r = N; // put a copy on the stack, private to the thread
      //@ close CCounter_shared_state(this)();
      mon.unlock();	
      //@ close CCounterInv(this);
      return r;
  } 

  public static void main(String[] args) 
  //@ requires true;
  //@ ensures true;
  {
       int MAX = 100;
       CCounter c = new CCounter(MAX);
       //@ assert [1]CCounterInv(c);
       
       //@ close Counter_frac(1);
       while( true ) 
       //@ invariant Counter_frac(?f) &*& [f]CCounterInv(c);
       {
          //@ open Counter_frac(f);
          //@ close Counter_frac(f/2);
          new Thread(new Inc(c)).start();
          //@ close Counter_frac(f/4);          
          new Thread(new Dec(c)).start();
          //@ close Counter_frac(f/4);          
       }
       
  }
}

//@ predicate Counter_frac(real r) = true;

//@ predicate IncInv(Inc o;) = o.c |-> ?v &*& v != null &*& [_]CCounterInv(v);

class Inc implements Runnable {
  //@ predicate pre() = IncInv(this);
  //@ predicate post() = true;
  
  CCounter c; 
  
  Inc(CCounter c) 
    //@ requires c != null &*& Counter_frac(?f) &*& [f]CCounterInv(c);
    //@ ensures  pre();
  {
    this.c = c;
    //@ close pre();
  }

  public void run()
  //@ requires pre();
  //@ ensures post();
  {
    c.inc();
    //@ close post();
  }
}

//@ predicate DecInv(Dec o;) = o.c |-> ?v &*& v != null &*& [_]CCounterInv(v);

class Dec implements Runnable {
  //@ predicate pre() = DecInv(this);
  //@ predicate post() = true;
  
  CCounter c; 
  
  Dec(CCounter c) 
    //@ requires c != null &*& Counter_frac(?f) &*& [f]CCounterInv(c);
    //@ ensures  pre();
  {
    this.c = c;
    //@ close pre();
  }

  public void run()
  //@ requires pre();
  //@ ensures post();
  {
    c.dec();
    //@ close post();
  }
}