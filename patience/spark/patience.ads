
package Patience with
  SPARK_Mode
is

   type Card is range 1..52;
   MaxNumCards : constant := 1000;
   type CardStack is array (Positive range <>) of Card;

   subtype CardIndex is Integer range -1..MaxNumCards;
   type CardArray is  array (0..MaxNumCards-1) of Card;
   type IndexArray is  array (0..MaxNumCards-1) of CardIndex;
   type IndexMatrix is array (0..MaxNumCards-1) of IndexArray;

   type State is
      record
         NumElts    : CardIndex;   -- number of cards already seen
         Values     : CardArray;   -- cards values seen, indexed in the order they have been seen,
                                   -- from 0 to NumElts-1
         NumStacks  : CardIndex;   -- number of stacks built so far
         StackSizes : IndexArray;  -- sizes of these stacks, numbered from 0 to NumStacks-1
         Stacks     : IndexMatrix; -- indexes of the cards in respective stacks
         PosStack   : IndexArray;  -- tables that given a card index, provides its position, i.e. in
         PosHeight  : IndexArray;  -- which stack it is and at which height
         Preds      : IndexArray;  -- predecessors of cards, i.e. for each card index i, Preds(i)
                                   -- provides an index of a card in the stack on the immediate left,
                                   -- whose value is smaller. Defaults to -1 if the card is on the
                                   -- leftmost stack
      end record;

   Null_State : constant State :=
     State'(NumElts    => 0,
            Values     => CardArray'(others => 1),
            NumStacks  => 0,
            StackSizes => IndexArray'(others => -1),
            Stacks     => IndexMatrix'(others => (others => -1)),
            Preds      => IndexArray'(others => -1),
            PosStack   => IndexArray'(others => -1),
            PosHeight  => IndexArray'(others => -1));

   function Inv(S : State) return Boolean is
      (0 <= S.NumStacks and S.NumStacks <= S.NumElts
         -- the number of stacks is less or equal the number of cards
         and
         (S.NumElts = 0 or else S.NumStacks > 0)
         -- when there is at least one card, there is at least one stack
         -- FIXME: is there an "imply" connective ?
         and
         (for all I in 0 .. S.NumStacks - 1 =>
            S.StackSizes(I) >= 1
            -- stacks are non-empty
            and
            S.StackSizes(I) <= S.NumElts
            -- stack sizes are at most the number of cards
            and
            (for all J in 0 .. S.StackSizes(I) - 1 =>
               0 <= S.Stacks(I)(J) and S.Stacks(I)(J) < S.NumElts)
            -- contents of stacks are valid card indexes
         )
         and
         (for all I in 0 .. S.NumElts - 1 =>
            -- FIXME: let pred = s.preds[i] in
            S.Preds(I) in -1 .. S.NumElts -1
            -- the predecessor is a valid index or -1
            and
            S.Preds(I) < I
            -- predecessor is always a smaller index
            and
            -- FIXME: let (is,_ip) = s.positions[i] in
            (if S.Preds(I) < 0 then S.PosStack(I) = 0
        -- if predecessor is -1 then I is in leftmost stack
            else
        S.Values(S.Preds(I)) < S.Values(I)
          -- if predecessor is not -1, it denotes a card with smaller value...
          and then S.PosStack(I) > 0
          -- ...the card is not on the leftmost stack...
          -- FIXME: let (ps,_pp) = s.positions[pred] in
          and then S.PosStack(S.Preds(I)) = S.Posstack(I) - 1
          -- ...and predecessor is in the stack on the immediate left
            )
          )
      );


   procedure PlayCard (C : in Card; S : in out State)
   with
     Pre => Inv(S) and S.NumElts < MaxNumCards,
     Post => Inv(S) and S.Values(S'Old.NumElts) = C and S.NumElts = S'Old.NumElts + 1;

   function PlayGame (Cards: CardStack) return State
   with
     Pre => Cards'Length <= MaxNumCards,
     Post => Inv(PlayGame'Result);

end Patience;

