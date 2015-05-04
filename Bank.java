
/*@
predicate AccountP(unit a,BankAccount c; unit b) = c != null &*& AccountInv(c,?n,?m) &*& b == unit;
@*/

class Bank {

BankAccount store[];
int nelems;
int capacity;

/*@
predicate BankInv(int n, int m) = 
     this.nelems |-> n &*& 
     this.capacity |-> m &*& 
     m > 0 &*&
     this.store |-> ?a &*&
     a.length == m &*&
     0 <= n &*& n<=m &*& 
     array_slice_deep(a, 0, n, AccountP, unit,_, _) &*&
     array_slice(a, n, m,?rest) &*& all_eq(rest, null) == true ;
@*/

public Bank(int siz)
//@ requires siz>0;
//@ ensures BankInv(0,siz);
{
  nelems = 0;
  capacity = siz;
  store = new BankAccount[siz];
}

void addnewAccount(int code)
//@ requires BankInv(?n,?m) &*& n < m &*& code >= 0;
//@ ensures  BankInv(n+1,m);
{

 	//@ array_slice_split(store, nelems,nelems+1);
 	BankAccount c = new BankAccount(code);
	store[nelems] = c;
	//@ array_slice_deep_close(store, nelems, AccountP, unit);
        nelems = nelems + 1;
}

int getbalance(int code)
//@ requires BankInv(?n,?m);
//@ ensures BankInv(n,m);
{
  int i = 0;

  //@ open BankInv(n,m);
  while (i < nelems)
  //@ invariant BankInv(n,m) &*& 0 <= i &*& i <= n;
  {
     if ( store[i].getcode() == code) {
     	return store[i].getbalance();
     }
     i = i + 1;
  }
  return -1;
}

}
