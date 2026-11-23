module

public import Development.EtaleCohomology.EtaleSheaves.ChernClassExistence
public import Development.EtaleCohomology.EtaleSheaves.ChernClassRootLocalization
public import Development.EtaleCohomology.TateTwists.EtaleKummerTriangleExists
public import Development.EtaleCohomology.TateTwists.EtalePrimitiveRootsExistLocally
public import Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertibleOrder
public import Development.EtaleCohomology.TateTwists.EtaleSheafSectionsGlueOfForgetIsSheaf
public import Development.EtaleCohomology.TateTwists.ExistsNaturalEtaleKummerDegreeOneValueOfRootsKum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
public import Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertib

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernClassEdgeValuesFromKummerTorsor

theorem kumT_ex_of (hk : LateralTheory.E.CupProductRingLaws.LeafKumTExists) : LateralTheory.EtaleFoundations.EtaleKummerTriangleExists := by
  intro q _
  unfold kumT
  exact pick_spec (hk q)

theorem prim_loc_of (hr : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc) : LateralTheory.EtaleFoundations.EtalePrimitiveRootsExistLocally :=
  LateralTheory.EtaleFoundations.etale_locally_roots_of_unity_structure_of_exists_and_kummer LateralTheory.EtaleFoundations.etale_locally_exists_primitive_root_of_unity_of_invertible_order hr

theorem etale_kummer_chern_edge_values_exist_of_local_roots_and_kummer_torsor (hr : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc) (hk : LateralTheory.E.CupProductRingLaws.LeafKumTExists) :
    LateralTheory.E.ChernClassExistence.EtaleKummerChernEdgeValuesExistNatural :=
  LateralTheory.EtaleFoundations.exists_natural_etale_kummer_degree_one_value_of_roots_kummer_gluing (prim_loc_of hr) (kumT_ex_of hk) LateralTheory.EtaleFoundations.etale_sheaf_sections_glue_of_forget_isSheaf

end LateralTheory.E.ChernClassEdgeValuesFromKummerTorsor
