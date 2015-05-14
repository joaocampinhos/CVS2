/*
VERIFAST example of verified Java progra
CVS course 14-15
Integrated Master in Computer Science and Engineering
@FCT UNL Luis Caires 2015
*/

/*@

predicate AccountInv(BankAccount ac; int b, int c) =
    ac.accountid |-> ?id
    &*&
    id >= 0
    &*&
    ac.balance |-> b
    &*&
    ac.climit |-> c
    &*&
    c >= 0
    &*&
    b + c >= 0;
@*/

public class BankAccount {

int balance;
int climit;
int accountid;

public BankAccount(int id)
//@ requires id >= 0;
//@ ensures AccountInv(this,0,0);
{
    balance = 0;
    climit = 0;
    accountid = id;
}

public void deposit(int v)
//@ requires AccountInv(this,?b,?c) &*& v >= 0;
//@ ensures AccountInv(this,b+v,c);
{
balance += v;
}

public void withdraw(int v)
//@ requires AccountInv(this,?b,?c) &*& v <= b + c;
//@ ensures AccountInv(this,b-v,c);

{
   balance  -= v;
}

public int getcode()
//@ requires AccountInv(this,?b,?c);
//@ ensures AccountInv(this,b,c);

{
   return accountid;
}

public int getbalance()
//@ requires AccountInv(this,?b,?c);
//@ ensures AccountInv(this,b,c) &*& result == b;

{
   return balance;
}

public void setclimit(int cl)
//@ requires AccountInv(this,?b,?c) &*& cl >= 0 &*& cl+b>=0;
//@ ensures AccountInv(this,b,cl);

{
    climit = cl;
}

public int getclimit()
//@ requires AccountInv(this,?b,?c);
//@ ensures AccountInv(this,b,c) &*& result == c;

{
   return climit;
}

static void main()
//@ requires true;
//@ ensures true;
{
BankAccount b1 = new BankAccount(1000);
b1.setclimit(500);

}

}
