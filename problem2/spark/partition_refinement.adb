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
              (for all J in Index => Contains (D, A(J)));

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
      Replace_Element (P, F(I), P_Elem);
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
            Replace_Element (P, J, P_Elem);

            P_Prime_Index := Partition_Index (Length (P));
            Append (P, P_Prime);

            for I in P_Prime.First .. P_Prime.Last loop
               F(I) := P_Prime_Index;
            end loop;
         end if;
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
   begin
      while Has_Element (X, C) loop
         Refine_One (A, D, P, F, Element (X, C));
         Next (X, C);
      end loop;
      Make_New_Partitions (P, F);
   end Refine;

end Partition_Refinement;