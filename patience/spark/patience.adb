
package body Patience
  with SPARK_Mode
is

   procedure PlayCard (C:in Card; S: in out State) is
      Idx, Pred, I : Integer;
      StackISize, TopStackI : CardIndex;
   begin
      Pred := -1;
      I := 0;
      while I < S.NumStacks loop
         StackISize := S.StackSizes(I);
         TopStackI := S.Stacks(I)(StackISize - 1);
         exit when C <= S.Values(TopStackI);
         pragma Loop_Invariant (I in 0 .. S.NumStacks - 1);
         pragma Loop_Invariant
           (for all K in 0 .. I =>
              C > S.Values(S.Stacks(K)(S.StackSizes(K) - 1)));
         Pred := TopStackI;
         I := I + 1;
      end loop;
      Idx := S.NumElts;
      S.Values(Idx) := C;
      S.NumElts := Idx + 1;
      if I = S.NumStacks then
         -- we add a new stack
         begin
            I := S.NumStacks;
            S.NumStacks := S.NumStacks + 1;
            S.StackSizes(I) := 1;
            S.Stacks(I)(0) := Idx;
         end;
      else
         -- we put c on top of stack i
         begin
            StackISize := S.StackSizes(I);
            S.StackSizes(I) := StackISize + 1;
            S.Stacks(I)(StackISize) := Idx;
         end;
      end if;
   end;



   function PlayGame (Cards: CardStack) return State
   is
      S : State := Null_State;
   begin
      for I in Cards'Range loop
         pragma Loop_Invariant (I in 1 .. Cards'Length);
         pragma Loop_Invariant (S.NumElts = I-1);
         pragma Loop_Invariant (Inv(S));
         PlayCard(Cards(I),S);
      end loop;
      return S;
   end PlayGame;

end Patience;
