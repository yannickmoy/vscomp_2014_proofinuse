with Ada.Text_IO; use Ada.Text_IO;
with Struct; use Struct;

procedure Simple is

      S : R := (X => 42);

begin
   Put_Line ("Test of a record update");
   Put_Line ("X= " & Integer'Image(S.X));
   IterIncr(S,10);
   Put_Line ("X= " & Integer'Image(S.X));
end Simple;


