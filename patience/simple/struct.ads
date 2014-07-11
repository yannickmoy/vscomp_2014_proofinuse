
package Struct with
  SPARK_Mode
is

type R is
   record
      X : Integer;
   end record;

function Inv(S:R) return Boolean is (S.X >= 0);

procedure Incr(S:in out R) with
  Post => Inv(S);

procedure IterIncr(S:in out R ; N:Integer) with
  Pre => Inv(S),
  Post => Inv(S);

function Toto(N:Integer) return R with
  Post => Inv(Toto'Result);

end Struct;
