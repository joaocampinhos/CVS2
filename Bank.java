/*
   CVS course 14-15
   Integrated Master in Computer Science and Engineering
   @FCT UNL
   João Campinhos 41721
   Pedro Durães   41911
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

  boolean addnewAccount(int code)
    //@ requires BankInv(this,?n,?m) &*& n < m &*& code >= 0;
    //@ ensures result ? BankInv(this,n,m) : BankInv(this,n+1,m);
  {
    //Códigos têm de ser únicos
    int i = 0;
    boolean rep = false;

    //@ open BankInv(this,n,m);
    while (i < nelems)
      //@ invariant BankInv(this,n,m) &*& 0 <= i &*& i <= n;
    {
      if ( store[i].getcode() == code) {
        rep = true;
      }
      i = i + 1;
    }

    if (!rep) {
      // @ array_slice_split(store, nelems,nelems+1);
      BankAccount c = new BankAccount(code);
      store[nelems] = c;
      //@ array_slice_deep_close(store, nelems, AccountP, unit);
      nelems = nelems + 1;
    }

    return rep;
  }



  /*------------------*\
   * Set Credit Limit *
  \*----------------- */

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
        if (store[i].getbalance() + cl >= 0) {
          store[i].setclimit(cl);
          return cl;
        }
      }
      i = i + 1;
    }
    return -1;
  }



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
    return Integer.MIN_VALUE;
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
        store[i].deposit(v);
        return v;
      }
      i = i + 1;
    }
    return -1;
  }



  /*----------------*\
   *    Withdraw    *
  \*----------------*/

  int withdraw(int code, int v)
    //@ requires BankInv(this,?n,?m) &*& v >= 0;
    //@ ensures BankInv(this,n,m);
  {
    int i = 0;

    //@ open BankInv(this,n,m);
    while (i < nelems)
      //@ invariant BankInv(this,n,m) &*& 0 <= i &*& i <= n;
    {
      if ( store[i].getcode() == code) {
        if (store[i].getbalance() + store[i].getclimit() >= v) {
          store[i].withdraw(v);
          return v;
        }
      }
      i = i + 1;
    }
    return -1;
  }



  /*----------------*\
   *    Transfer    *
  \*----------------*/

  boolean transfer(int code_from, int code_to, int v)
    //@ requires BankInv(this,?n,?m) &*& v >= 0;
    //@ ensures BankInv(this,n,m);
  {
    int i = 0;
    int from = -1;
    int to = -1;

    //@ open BankInv(this,n,m);
    while (i < nelems)
      //@ invariant BankInv(this,n,m) &*& 0 <= i &*& i <= n;
    {
      if ( store[i].getcode() == code_from) {
        from = i;
      }
      if ( store[i].getcode() == code_to) {
        to = i;
      }
      i = i + 1;
    }

    int parcial = withdraw(from, v);

    if (parcial != -1) {
      deposit(to, v);
      return true;
    }

    return false;
  }



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
          store[i] = store[nelems-1];
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
