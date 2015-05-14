/*
   VERIFAST example of verified Java progra
   CVS course 14-15
   Integrated Master in Computer Science and Engineering
   @FCT UNL Luis Caires 2015
*/

/*@
  predicate AccountP(unit a,BankAccount c; int n) =
    c != null &*& AccountInv(c,n,?m);
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
    array_slice(a, n, m,?rest) &*& all_eq(rest, null) == true ;
@*/


class Bank {

  BankAccount store[];
  int nelems;
  int capacity;


  public Bank(int siz)
    //@ requires siz>0;
    //@ ensures BankInv(this,0,siz);
  {
    nelems = 0;
    capacity = siz;
    store = new BankAccount[siz];
  }



  /*-----------------*\
   * Add New Account *
  \*-----------------*/

  void addnewAccount(int code)
    //@ requires BankInv(this,?n,?m) &*& n < m &*& code >= 0;
    //@ ensures  BankInv(this,n+1,m);
  {

    // @ array_slice_split(store, nelems,nelems+1);
    BankAccount c = new BankAccount(code);
    store[nelems] = c;
    //@ array_slice_deep_close(store, nelems, AccountP, unit);
    nelems = nelems + 1;
  }



  /*------------------*\
   * Set Credit Limit *
  \*----------------- */

  /*
  int setclimit(int code, int cl)
    //@ requires BankInv(this,?n,?m) &*& cl >= 0;
    //@ ensures BankInv(this,n,m);
  {
    int i = 0;

    //@ open BankInv(this,n,m);
    while (i < nelems)
      //@ invariant BankInv(this,n,m) &*& 0 <= i &*& i <= n;
    {
      if ( store[i].getcode() == code) {
        return store[i].setclimit(cl);
        return cl;
      }
      i = i + 1;
    }
    return -1;
  }
  */



  /*------------------*\
   * Get Credit Limit *
  \*----------------- */

  int getclimit(int code)
    //@ requires BankInv(this,?n,?m);
    //@ ensures BankInv(this,n,m);
  {
    int i = 0;

    //@ open BankInv(this,n,m);
    while (i < nelems)
      //@ invariant BankInv(this,n,m) &*& 0 <= i &*& i <= n;
    {
      if ( store[i].getcode() == code) {
        return store[i].getclimit();
      }
      i = i + 1;
    }
    return -1;
  }



  /*-----------------*\
   *   Get Balance   *
  \*-----------------*/

  int getbalance(int code)
    //@ requires BankInv(this,?n,?m);
    //@ ensures BankInv(this,n,m);
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



  /*---------------*\
   *    Deposit    *
  \*---------------*/

  int deposit(int code, int v)
    //@ requires BankInv(this,?n,?m) &*& v >= 0;
    //@ ensures BankInv(this,n,m);
  {
    int i = 0;

    //@ open BankInv(this,n,m);
    while (i < nelems)
      //@ invariant BankInv(this,n,m) &*& 0 <= i &*& i <= n;
    {
      if ( store[i].getcode() == code) {
        return store[i].deposit(v);
        return v;
      }
      i = i + 1;
    }
    return -1;
  }



  /*----------------*\
   *    Withdraw    *
  \*----------------*/




  /*----------------*\
   *    Transfer    *
  \*----------------*/




  /*----------------*\
   * Remove Account *
  \*----------------*/

  int removeAccount(int code)
    //@ requires BankInv(this,?n,?m);
    //@ ensures result == 0 ? BankInv(this,n-1,m) : BankInv(this,n,m);
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



  void extendstore()
    //@ requires BankInv(this,?n,?m);
    //@ ensures BankInv(this,n,2*m);
  {
    int i = 0;
    BankAccount newstore[] = new BankAccount[capacity*2];
    //@ open BankInv(this,n,m);
    while (i < nelems)
      /*@  invariant
        this.nelems |-> n &*&
        this.capacity |-> m &*&
        this.store |-> ?a &*&
        a.length == m &*&
        0 <= n &*& n<=m &*&
        array_slice(a, 0, i,?r1) &*& all_eq(r1, null) == true  &*&
        array_slice_deep(a, i, n, AccountP, unit,_,?bs) &*&
        array_slice(a, n, m,?rest) &*& all_eq(rest, null) == true &*&
        array_slice_deep(newstore, 0, i, AccountP, unit,_,_) &*&
        array_slice(newstore, i, m*2,?r2) &*& all_eq(r2, null) == true
        &*& 0 <= i &*& i <= n;
        @*/
    {
      newstore[i] = store[i];
      store[i] = null;
      i++;
    }
    capacity = 2*capacity;
    store = newstore;
    return;
  }

}
