/*
Starting point for exercise of Lab Session 6.
CVS course - Integrated Master in Computer Science and Engineering
@FCT UNL 2018
*/

/*@
predicate AccountInv(BankAccount c; int limit, int balance, int id) = 
      c.balance |-> balance
  &*& c.climit |-> limit
  &*& c.accountid |-> id
  &*& 0 <= id
  &*& 0 <= limit
  &*& 0 <= balance + limit 
;
@*/

public class BankAccount {

  int balance;
  int climit;
  int accountid;

  public BankAccount(int id)
    //@ requires 0 <= id;
    //@ ensures  AccountInv(this,0,0,id);
  {
      balance = 0;
      climit = 0;
      accountid = id;
      // @ close AccountInv(this,_,_,_);
  }

  public void deposit(int v)
    //@ requires AccountInv(this,?c,?b,?id) &*& 0 <= v;
    //@ ensures  AccountInv(this,c,b+v,id);
  {
    balance += v;
  }

  public void withdraw(int v)
    //@ requires AccountInv(this,?c,?b,?id) &*& 0 <= v &*& v <= b + c ;
    //@ ensures  AccountInv(this,c,b-v,id);
  {
     balance  -= v;
  }

  public int getcode()
    //@ requires AccountInv(this,?c,?b,?id);
    //@ ensures  AccountInv(this,c,b,id) &*& result == id;
  {
     return accountid;
  }

  public int getbalance()
    //@ requires AccountInv(this,?c,?b,_);
    //@ ensures  AccountInv(this,c,b,_) &*& result == b;
  {
     return balance;
  }

  public void setclimit(int cl)
    //@ requires AccountInv(this,?c,?b,?id) &*& 0 <= cl &*& 0 <= b + cl;
    //@ ensures  AccountInv(this,cl,b,id);  
  {
      climit = cl;
  }

  public int getclimit()
    //@ requires AccountInv(this,?c,?b,?id);
    //@ ensures  AccountInv(this,c,b,id) &*& result == c;  
  {
     return climit;
  }

  static void main()
    //@ requires true;
    //@ ensures  true;
  {
    BankAccount b1 = new BankAccount(123);
    b1.deposit(1000);
    b1.setclimit(500);
    b1.withdraw(1450);
    //@ open AccountInv(b1,_,_,_);
    int n = b1.getcode();
    //@ assert n == 123;
    if( b1.getbalance() >= -200 )
    	b1.setclimit(200);
  }
}