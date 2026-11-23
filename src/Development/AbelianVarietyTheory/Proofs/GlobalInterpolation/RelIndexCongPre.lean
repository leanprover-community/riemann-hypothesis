module

public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MyTiedNotMeasTupleTied
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast

@[expose] public section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory.CongIndex

theorem relIndex_congPre (O K : Type) [CommRing O] [IsLocalRing O] [CommRing K] (ι : O →+* K)
    (hι : Function.Injective ι) (n : ℕ) (H : Subgroup (GL (Fin n) (O ⧸ IsLocalRing.maximalIdeal O))) :
    (congPre ι (IsLocalRing.maximalIdeal O) H).relIndex (bc (n := Fin n) ι).range = H.index := by
  have hinj : Function.Injective (bc (n := Fin n) ι) := by
    intro g h e
    apply Units.ext
    ext a b
    apply hι
    exact congrArg (fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K) a b) e
  have hs : Function.Surjective (redGL (n := Fin n) (IsLocalRing.maximalIdeal O)) :=
    GlobalTheory.MeasTupleEq.map_residue_surjective O n
  unfold congPre
  rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hinj,
    Subgroup.relIndex_top_right, Subgroup.index_comap_of_surjective _ hs]

end GlobalTheory.CongIndex
