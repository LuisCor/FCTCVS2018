/*
Starting point for exercise of Lab Session 6.
CVS course - Integrated Master in Computer Science and Engineering
@FCT UNL Luis Caires 2015
*/

/*@
predicate AccountP(unit a,BankAccount c; int n) = c != null &*& AccountInv(c,n,?m);
@*/

/*@
predicate BankInv(Bank bk; int n, int m) = 
     bk.nelems |-> n &*& 
     bk.capacity |-> m &*& 
     m > 0 &*&
     bk.store |-> ?a &*&
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
  //@ ensures BankInv(this,0,size);
  {
    nelems = 0;
    capacity = siz;
    store = new BankAccount[siz];
  }

  void addnewAccount(int code)
     //@ requires BankInv(this,?n, ?m) &*& code >= 0;
     //@ ensures BankInv(this,n+1,m);
  
  {
   	BankAccount c = new BankAccount(code);
  	store[nelems] = c;
    nelems = nelems + 1;
  }

  int getbalance(int code)
     //@ requires BankInv(this,?n, ?m);
     //@ ensures BankInv(this,n+1,m);
  
  {
    int i = 0;

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
  {
    int i = 0;
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
