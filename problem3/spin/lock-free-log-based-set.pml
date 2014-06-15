
#define SIZE 2
#define THREAD_COUNT 2

short log[SIZE] = 0;

byte gc = 0
byte tl = 0;
byte hd = 0;

byte ht[THREAD_COUNT] = SIZE;

mtype = { not_in_set, in_set, changed };

mtype value_in_set[THREAD_COUNT] = not_in_set;

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
  byte h;
  bool success;
  short cmpXchg_res;

  grab(h, hd);

  do
  :: h < SIZE;
     atomic {
            assert(h >= gc); /* prove memory-safety */
            cmpXchg(log[h], 0, val)
     };
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
  byte t, i;
  short x;
  byte abs_res;

  grab(t, tl);

  i = hd;
  do
  :: i != t;
     atomic {
            assert(i-1 >= gc); /* prove memory-safety */
            x = log[i-1]
     };
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
  byte t = tl;
  byte i;
  byte min_res;
  byte cmpXchg_res;

  for (i : 0 .. THREAD_COUNT - 1) {
    min(t, ht[i]);
    t = min_res
  };

  byte g;

  g = gc;

  if
  :: g < t -> cmpXchg(gc, g, t)
  :: else -> skip
  fi
}

inline possible_collect() {
  if
  :: true -> collect()
  :: true -> skip
  fi
}

init /* will have _pid = 0 */
{
  pid i;

  atomic {
         for (i : 0 .. THREAD_COUNT - 1) {
             run thread() /* will have _pid \in 1 .. THREAD_COUNT */
         };

         run environment()

         /*run sequential_test()*/
  }
}

proctype thread()
{
  bool do_return_res;
  byte thr_id = 0;
  mtype was_in_set;

  do
  :: atomic { (value_in_set[thr_id] == in_set
               || value_in_set[thr_id] == not_in_set);
               was_in_set = value_in_set[thr_id] } ->
                lookup(thr_id+1);
                assert(!(was_in_set == in_set) || do_return_res == true);
                assert(!(was_in_set == not_in_set) || do_return_res == false)
  :: atomic { value_in_set[thr_id] == not_in_set;
              value_in_set[thr_id] = changed } ->
               update(thr_id+1);
               value_in_set[thr_id] = in_set
  :: atomic { value_in_set[thr_id] == in_set;
              value_in_set[thr_id] = changed } ->
               update(-(thr_id+1));
               value_in_set[thr_id] = not_in_set
  :: thr_id < THREAD_COUNT - 1 -> thr_id++
  :: thr_id == THREAD_COUNT - 1 -> thr_id = 0
  :: true -> collect()
  :: true -> skip
  od
}

proctype environment()
{
  do
  :: true ->
       atomic {
         byte i;
         byte abs_res;
         byte abs1, abs2;

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
  short do_return_res;

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
