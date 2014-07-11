
package body Struct with
  SPARK_Mode
is


   procedure Incr(S:in out R) is
   begin
      S.X := 0;
   end;

   procedure IterIncr(S:in out R ; N:Integer) is
   begin
      for I in 1 .. N loop
         Incr(S);
      end loop;
   end;
   
   function Toto(N:Integer) return R is
      S : R := (X => 0);
   begin
      for I in 1..12 loop
         pragma Loop_Invariant (Inv(S));
         IterIncr(S,10);
      end loop;
      return S;
   end Toto;

end Struct;
