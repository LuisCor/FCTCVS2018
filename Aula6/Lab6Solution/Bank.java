/*
Starting point for exercise of Lab Session 6.
CVS course - Integrated Master in Computer Science and Engineering
@FCT UNL Luis Caires 2015
*/

/*@
predicate AccountP(unit a,BankAccount c; int n) = c != null &*& AccountInv(c,n,?m,_);
@*/

/*@
predicate BankInv(Bank bk; int n, int m) = 
     bk.nelems |-> n &*& 
     bk.capacity |-> m &*& 
     bk.store |-> ?a &*&
     m > 0 &*&
     a != null &*&
     a.length == m &*&
     0 <= n &*& n<=m &*& 
     array_slice_deep(a, 0, n, AccountP, unit,_,?bs) &*&
     array_slice(a, n, m,?rest) &*& 
     all_eq(rest, null) == true ;
@*/


class Bank {

  BankAccount store[];
  int nelems;
  int capacity;

  public Bank(int size)
    //@ requires 0 < size;
    //@ ensures  BankInv(this,0,size);
  {
    nelems = 0;
    capacity = size;
    store = new BankAccount[size];
  }

  void addnewAccount(int code)
    //@ requires BankInv(this,?n,?m) &*& n < m &*& code >= 0;
    //@ ensures  BankInv(this,n+1,m);  
  {
    BankAccount c = new BankAccount(code);
    store[nelems] = c;
    nelems = nelems + 1;
  }

  int getbalance(int code)
    //@ requires BankInv(this,?n,?m);
    //@ ensures  BankInv(this,n,m);    
  {
    int i = 0;
    //@ open BankInv(this,n,m);
    while (i < nelems)
    //@ invariant BankInv(this,n,m) &*& 0 <= i &*& i <= n;
    {
       if ( store[i].getcode() == code) {
       	return store[i].getbalance();
       }
       i = i + 1;
    }
    return -1;
  }

  int removeAccount(int code)
    //@ requires BankInv(this,?n,?m);
    //@ ensures  result == -1 ? BankInv(this,n,m) : BankInv(this,n-1,m);    
  {
    int i = 0;
    //@ open BankInv(this,n,m);
    while (i < nelems)
    //@ invariant BankInv(this,n,m) &*& 0 <= i &*& i <= n;
    {
       if ( store[i].getcode() == code) {
       	   if (i<nelems-1) {
       	     store[i] == store[nelems-1];
       	   }
       	   nelems = nelems - 1;
       	   store[nelems] = null;
       	   return 0;
       }
       i = i + 1;
    }
    return -1;
  }
}