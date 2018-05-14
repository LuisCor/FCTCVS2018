/*@ 
    predicate BCounterInv(BCounter c; int v,int m) = 
        c.N |-> v &*& c.MAX |-> m &*& v>=0 &*& v<=m;
@*/
class BCounter {
  int N;
  int MAX;

  BCounter(int max)
  //@ requires 0 <= max;
  //@ ensures BCounterInv(this,0,max);
  { N = 0 ; MAX = max; }

  void inc()
  //@ requires BCounterInv(this,?n,?m) &*& n < m;
  //@ ensures BCounterInv(this,n+1,m);
  { N++; } 

  void dec()
  //@ requires BCounterInv(this,?n,?m) &*& n > 0;
  //@ ensures BCounterInv(this,n-1,m);
  { N--; } 
  
  int get()
  //@ requires BCounterInv(this,?n,?m);
  //@ ensures BCounterInv(this,n,m) &*& 0<=result &*& result<=m;
  { return N; } 

  public static void main(String[] args) 
  //@ requires true;
  //@ ensures true;
  {
       int MAX = 100;
       BCounter c = new BCounter(MAX);
       //@ assert BCounterInv(c,0,MAX);
       //giveaway(c); // potentially give other thread access to c
        if (c.get() < MAX) {
            //@ assert BCounterInv(c,?v,MAX) &*& v < MAX;
            c.inc(); // not safe any more as other thread may have acted
        }
  }
}