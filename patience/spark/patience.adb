
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
         pragma Loop_Invariant (I in 0 .. S.NumStacks);
         pragma Loop_Invariant 
           (
            (if I = 0 then Pred = -1 else
           -- let stack_im1 = s.stacks[i-1] in
           -- let stack_im1_size = s.stack_sizes[i-1] in
           -- let top_stack_im1 = stack_im1[stack_im1_size - 1] in
           (Pred in 0 .. S.NumElts - 1
              and then
              Pred = S.Stacks(I-1)(S.StackSizes(I-1)-1)
            and then
              C > S.Values(Pred)
              and then
              -- let (ps,_pp) = s.positions[!pred] in
              S.PosStack(Pred) = I-1
           )));
           StackISize := S.StackSizes(I);
           TopStackI := S.Stacks(I)(StackISize - 1);
           exit when C <= S.Values(TopStackI);
           pragma Assert (0 <= TopStackI and TopStackI < S.Numelts);
           pragma Assert
             (-- let (is,ip) = s.positions[top_stack_i] in
              0 <= S.PosStack(TopStackI) and then
                S.PosStack(TopStackI) < S.NumStacks and then
                0 <= S.PosHeight(TopStackI) and then
                 S.PosHeight(TopStackI) < S.StackSizes(S.PosStack(TopStackI)) and then
                 S.Stacks(S.PosStack(TopStackI))( S.PosHeight(TopStackI)) = TopStackI and then
                S.PosStack(TopStackI) = I and then S.PosHeight(TopStackI) = StackISize - 1
             );
           Pred := TopStackI;
           I := I + 1;
            end loop;
      Idx := S.NumElts;
      S.Values(Idx) := C;
      S.NumElts := Idx + 1;
      S.Preds(Idx) := Pred;
      if I = S.NumStacks then
         -- we add a new stack
         begin
            I := S.NumStacks;
            S.NumStacks := S.NumStacks + 1;
            S.StackSizes(I) := 1;
            S.Stacks(I)(0) := Idx;
            S.PosStack(Idx) := I;
            S.PosHeight(Idx) := 0;
         end;
      else
         -- we put c on top of stack i
         begin
            StackISize := S.StackSizes(I);
            S.StackSizes(I) := StackISize + 1;
            S.Stacks(I)(StackISize) := Idx;
            S.PosStack(Idx) := I;
            S.PosHeight(Idx) := StackISize;
         end;
      end if;
   end;



   function PlayGame (Cards: CardStack) return State
   is
      S : State := Null_State;
   begin
      for I in Cards'Range loop
         pragma Loop_Invariant (S.NumElts = I-1);
         pragma Loop_Invariant (Inv(S));
         PlayCard(Cards(I),S);
      end loop;
      return S;
   end PlayGame;

end Patience;
