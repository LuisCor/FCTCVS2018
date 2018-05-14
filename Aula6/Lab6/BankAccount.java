/*
Starting point for exercise of Lab Session 6.
CVS course - Integrated Master in Computer Science and Engineering
@FCT UNL 2018
*/


public class BankAccount {

  int balance;
  int climit;
  int accountid;

  public BankAccount(int id)
  {
      balance = 0;
      climit = 0;
      accountid = id;
  }

  public void deposit(int v)
  {
  balance += v;
  }

  public void withdraw(int v)
  {
     balance  -= v;
  }

  public int getcode()
  {
     return accountid;
  }

  public int getbalance()
  {
     return balance;
  }

  public void setclimit(int cl)
  {
      climit = cl;
  }

  public int getclimit()
  {
     return climit;
  }

  static void main()
  {
    BankAccount b1 = new BankAccount(1000);
    b1.setclimit(500);
  }
}
