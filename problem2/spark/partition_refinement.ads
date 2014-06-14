with Ada.Containers.Formal_Ordered_Maps;
with Ada.Containers.Formal_Vectors;
with Ada.Containers.Formal_Doubly_Linked_Lists;
use Ada.Containers;

package Partition_Refinement with
  SPARK_Mode
is

   N : constant := 6;
   type Index_Count is range 0 .. N;
   subtype Index is Index_Count range 0 .. N - 1;
   type Set is array (Index) of Positive;

   function Eq_Positive (Left, Right : Positive) return Boolean is (Left = Right);
   package Partitioning_Sets is new
     Formal_Doubly_Linked_Lists (Element_Type => Positive,
                                 "="          => Eq_Positive);
   subtype Partitioning_Set is Partitioning_Sets.List;
   use Partitioning_Sets;

   function Lt_Positive (Left, Right : Positive) return Boolean is (Left < Right);
   function Eq_Index (Left, Right : Index) return Boolean is (Left = Right);
   package Inverse_Sets is new
     Formal_Ordered_Maps (Key_Type     => Positive,
                          ELement_Type => Index,
                          "<"          => Lt_Positive,
                          "="          => Eq_Index);
   subtype Inverse_Set is Inverse_Sets.Map;
   use Inverse_Sets;

   type Interval is record
      First : Index;
      Last  : Index;
      Count : Index_Count;
   end record;
   type Partition_Index is range 0 .. 10_000;
   function Eq_Interval (Left, Right : Interval) return Boolean is (Left = Right);
   package Partitions is new
     Formal_Vectors (Index_Type   => Partition_Index,
                     Element_Type => Interval,
                     "="          => Eq_Interval);
   subtype Partition is Partitions.Vector;
   use Partitions;

   type Inverse_Partition is array (Index) of Partition_Index;

   procedure Refine
     (A : in out Set;
      D : in out Inverse_Set;
      P : in out Partition;
      F : in out Inverse_Partition;
      X : in     Partitioning_Set);

end Partition_Refinement;