
#define SIZE 3
#define THREAD_COUNT 3

/* Spin initializes everything to 0 by default */
int log[SIZE];

int gc, tl, hd;

int ht[THREAD_COUNT];

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
     cmpXchg(log[h], 0, val);
     success = !cmpXchg_res;
     cmpXchg(hd, h, h+1);
     if
     :: success -> do_return(0);
                   break
     :: else -> advance(h, hd)
     fi
   :: else ->
end_size_reached:
             0 == 1 /* we reached SIZE, stop process */
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
             ht[i] = SIZE
         }

         /*for (i : 0 .. THREAD_COUNT - 1) {
             run thread()
         }*/

         run sequential_test()
  }
}

proctype thread() /* will have _pid \in 1 .. THREAD_COUNT */
{
  int do_return_res;

  do
  :: true -> update(1)
  :: true -> update(-1)
  :: true -> lookup(1)
  od
}

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
