
#define SIZE 2
#define THREAD_COUNT 2

int log[SIZE] = 0;

int gc = 0
int tl = 0;
int hd = 0;

int ht[THREAD_COUNT] = SIZE;

inline abs(x) {
  d_step {
    if
    :: x < 0 -> abs_res = -x
    :: else -> abs_res = x
    fi
  }
}

inline min(x, y) {
  d_step {
    if
    :: x < y -> min_res = x
    :: else -> min_res = y
    fi
  }
}

inline cmpXchg(loc, old, new) {
  d_step {
    if
    :: loc == old -> loc = new; cmpXchg_res = old
    :: else -> cmpXchg_res = loc
    fi
  }
}

inline do_return(v) {
  ht[_pid-1] = SIZE;
  do_return_res = v
}

inline advance(local_var, var) {
  local_var = var;
  ht[_pid-1] = local_var
}

inline grab(local_var, var) {
  advance(local_var, var);
  advance(local_var, var)
}

inline update(val) {
  int h;
  bool success;
  int cmpXchg_res;

  grab(h, hd);

  do
  :: h < SIZE;
     assert(h >= gc); /* prove memory-safety */
     cmpXchg(log[h], 0, val);
     success = !cmpXchg_res;
     cmpXchg(hd, h, h+1);
     if
     :: success -> do_return(0);
                   break
     :: else -> advance(h, hd)
     fi
   :: else ->
end_end_of_log_reached:
             0 == 1 /* we reached end of log, stop process */
  od
}

inline lookup(val) {
  int t, i;
  int x;
  int abs_res;

  grab(t, tl);

  i = hd;
  do
  :: i != t;
     assert(i-1 >= gc); /* prove memory-safety */
     x = log[i-1];
     abs(x);
     if
     :: abs_res != val -> i--
     :: else -> goto exit
     fi
  :: else -> break
  od;

exit:
  do_return(i != t && 0 < x)
}

inline collect() {
  int t = tl;
  int i;
  int min_res;
  int cmpXchg_res;

  for (i : 0 .. THREAD_COUNT - 1) {
    min(t, ht[i]);
    t = min_res
  };

  int g;

  g = gc;

  if
  :: g < t -> cmpXchg(gc, g, t)
  :: else -> skip
  fi
}

init /* will have _pid = 0 */
{
  int i;

  atomic {
         for (i : 0 .. THREAD_COUNT - 1) {
             run thread()
         };

         run environment()

         /*run sequential_test()*/
  }
}

proctype thread() /* will have _pid \in 1 .. THREAD_COUNT */
{
  int do_return_res;
  int value;

  value = _pid + 1;

  do
  :: true -> update(value);
             assert(do_return_res == false);

             lookup(value);
             assert(do_return_res == true);

             update(-value);
             assert(do_return_res == false);

             lookup(value);
             assert(do_return_res == false)
  :: true -> collect()
  :: true -> break
  od
}

proctype environment()
{
  do
  :: true ->
       atomic {
         int i;
         int abs_res;
         int abs1, abs2;

         i = tl + 1;
         do
         :: i < hd -> abs(log[tl]);
                      abs1 = abs_res;
                      abs(log[i]);
                      abs2 = abs_res;
                      if
                      :: abs1 == abs2 -> tl++; break
                      :: else -> break
                      fi
         :: i == SIZE -> goto exit
         :: else -> break
         od
       }
   od
exit:
}

/*
proctype sequential_test()
{
  int do_return_res;

  lookup(1);
  assert(do_return_res == false);

  update(1);
  assert(do_return_res == false);

  lookup(1);
  assert(do_return_res == true);

  update(-1);
  assert(do_return_res == false);

  lookup(1);
  assert(do_return_res == false);

  collect()
end:
}
*/
