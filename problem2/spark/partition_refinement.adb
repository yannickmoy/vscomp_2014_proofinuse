package body Partition_Refinement with
  SPARK_Mode
is

   -----------------------
   -- Local subprograms --
   -----------------------

   procedure Swap
     (A    : in out Set;
      J, K : Index)
   with
     Post => A = A'Old'Update (J => A'Old(K), K => A'Old(J));

   procedure Refine_One
     (A      : in out Set;
      D      : in out Inverse_Set;
      P      : in out Partition;
      F      : in     Inverse_Partition;
      X_Elem : in Positive)
   with
      Pre  => Contains (D, X_Elem) and then
              F(Element (D, X_Elem)) in 0 .. Partition_Index'Base (Length (P)) - 1 and then
              Element (P, F(Element (D, X_Elem))).First + Element (P, F(Element (D, X_Elem))).Count in Index and then
              (for all J in Index => Contains (D, A(J))),
      Post => A = A'Old'Update
                (Element (D, X_Elem)'Old =>
                   A(Element (P, F(Element (D, X_Elem))).First + Element (P, F(Element (D, X_Elem))).Count)'Old,
                 Index'(Element (P, F(Element (D, X_Elem))).First + Element (P, F(Element (D, X_Elem))).Count)'Old =>
                   A(Element (D, X_Elem))'Old) and then
              Capacity (P) = Capacity (P)'Old and then
              Length (P) = Length (P)'Old and then
              (for all J in 0 .. Partition_Index(Length (P)) - 1 =>
                 Element (P, J).First = Element (P'Old, J).First) and then
              (for all J in 0 .. Partition_Index(Length (P)) - 1 =>
                 Element (P, J).Count = Element (P'Old, J).Count + (if J = F(Element (D, X_Elem)) then 1 else 0)) and then
              (for all J in Index => Contains (D, A(J))) and then
              (for all C in D => A (Element (D, C)) = Key (D, C)) and then
              (for all C in D'Old => Has_Element (D, C));

   procedure Make_New_Partitions
     (P : in out Partition;
      F : in out Inverse_Partition)
   with
      Pre  => 2 * Length (P) <= Capacity (P) and then
              Length (P) <= Count_Type(Partition_Index'Last / 2);

   ----------
   -- Swap --
   ----------

   procedure Swap
     (A    : in out Set;
      J, K : Index)
   is
      Tmp : constant Positive := A(J);
   begin
      A(J) := A(K);
      A(K) := Tmp;
   end Swap;

   ----------------
   -- Refine_One --
   ----------------

   procedure Refine_One
     (A      : in out Set;
      D      : in out Inverse_Set;
      P      : in out Partition;
      F      : in     Inverse_Partition;
      X_Elem : in Positive)
   is
      I : constant Index := Element (D, X_Elem);
      P_Elem : Interval := Element (P, F(I));
      J : constant Index := P_Elem.First + P_Elem.Count;
   begin
      Swap (A, I, J);
      Replace (D, A(I), I);
      Replace (D, A(J), J);
      P_Elem.Count := P_Elem.Count + 1;

      --  Replace_Element does not modify the capacity of the vector, but SPARK GPL 2014 does not prove it.
      --  Use a local assumption to convey this information.
      declare
         Save_Capacity : constant Count_Type := Capacity (P);
      begin
         Replace_Element (P, F(I), P_Elem);
         pragma Assume (Capacity (P) = Save_Capacity);
      end;
   end Refine_One;

   -------------------------
   -- Make_New_Partitions --
   -------------------------

   procedure Make_New_Partitions
     (P : in out Partition;
      F : in out Inverse_Partition)
   is
      P_Elem, P_Prime : Interval;
      P_Prime_Index : Partition_Index;
   begin
      for J in 0 .. Partition_Index'Base (Length (P)) - 1 loop
         P_Elem := Element (P, J);
         if P_Elem.Count in 1 .. P_Elem.Last - P_Elem.First then
            P_Prime := Interval'(First => P_Elem.First + P_Elem.Count,
                                 Last  => P_Elem.Last,
                                 Count => 0);
            P_Elem.Last := P_Elem.First + P_Elem.Count - 1;
            P_Elem.Count := 0;

            --  Replace_Element does not modify the capacity of the vector, but SPARK GPL 2014 does not prove it.
            --  Use a local assumption to convey this information.
            declare
               Save_Capacity : constant Count_Type := Capacity (P);
            begin
               Replace_Element (P, J, P_Elem);
               pragma Assume (Capacity (P) = Save_Capacity);
            end;

            P_Prime_Index := Partition_Index (Length (P));
            Append (P, P_Prime);

            for I in P_Prime.First .. P_Prime.Last loop
               F(I) := P_Prime_Index;
            end loop;
         end if;

         --  Intermediate assertion used to decrease time to prove loop invariant
         pragma Assert (for all K in J + 1 .. Partition_Index'Base (Length (P)'Loop_Entry) - 1 => Element (P, K) = Element (P'Loop_Entry, K));

         pragma Loop_Invariant (Capacity (P) = Capacity (P)'Loop_Entry);
         pragma Loop_Invariant (Length (P) - Length (P)'Loop_Entry in 0 .. Count_Type(J) + 1);
         pragma Loop_Invariant (for all K in J + 1 .. Partition_Index'Base (Length (P)'Loop_Entry) - 1 => Element (P, K) = Element (P'Loop_Entry, K));
      end loop;
   end Make_New_Partitions;

   ------------
   -- Refine --
   ------------

   procedure Refine
     (A : in out Set;
      D : in out Inverse_Set;
      P : in out Partition;
      F : in out Inverse_Partition;
      X : in     Partitioning_Set)
   is
      C : Partitioning_Sets.Cursor := First (X);

      pragma Warnings (Off, "statement has no effect", Reason => "ghost code");
      D_Old : constant Inverse_Set := D;
      pragma Warnings (On, "statement has no effect", Reason => "ghost code");

   begin
      while Has_Element (X, C) loop

         pragma Assert (Has_Element (D, (Find (D_Old, Element (X, C)))));
         --  This assumption is a logical consequence of the assertion above, that SPARK GPL 2014 does not prove.
         pragma Assume (Contains (D, Element (X, C)));
         Refine_One (A, D, P, F, Element (X, C));
         Next (X, C);

         --  Part of the loop invariant, requires changes in Refine_One's postcondition for being provable
         pragma Assert (for all J in 0 .. Partition_Index(Length (P)) - 1 => Element (P, J).First + Element (P, J).Count in Index);

         pragma Loop_Invariant (Capacity (P) = Capacity (P)'Loop_Entry);
         pragma Loop_Invariant (Length (P) = Length (P)'Loop_Entry);
         pragma Loop_Invariant (for all C in D => A (Element (D, C)) = Key (D, C));
         pragma Loop_Invariant (for all C in D_Old => Has_Element (D, C));
         pragma Loop_Invariant (for all C in X => Has_Element (D, (Find (D_Old, Element (X, C)))));
         pragma Loop_Invariant (for all J in 0 .. Partition_Index(Length (P)) - 1 => Element (P, J).First + Element (P, J).Count in Index);
         pragma Loop_Invariant (for all J in Index => Contains (D, A(J)));
      end loop;

      Make_New_Partitions (P, F);
   end Refine;

end Partition_Refinement;
