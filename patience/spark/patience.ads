
package Patience with
  SPARK_Mode
is

   type Card is range 1..52;
   MaxNumCards : constant := 1000;
   type CardStack is array (Integer range <>) of Card;

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
      end record;


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
            (for all J in 0 .. S.StackSizes(I) - 1 =>
               0 <= S.Stacks(I)(J) and S.Stacks(I)(J) < S.NumElts)
            -- contents of stacks are valid card indexes
         )
      );


   procedure PlayCard (C : in Card; S : in out State)
   with
     Pre => Inv(S) and S.NumElts < MaxNumCards,
     Post => Inv(S) and S.Values(S'Old.NumElts) = C and S.NumElts = S'Old.NumElts + 1;

   function PlayGame (Cards: CardStack) return State;

end Patience;

