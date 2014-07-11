
package Struct is
  
type R is
   record
      X : Integer;
   end record;

procedure Incr(S:in out R) with
  Post => S.X = S.X'Old + 1;

end Struct;
