module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SiegelWeilVolume.MulTupApplyEqSum
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SiegelWeilVolume.IsFibreFamilyReindex

@[expose] public section

noncomputable section

namespace PI.NcVal.OmVc1

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.DegenerateSiegelWeil.Scale
open scoped TensorProduct

theorem gram_entry {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) (n M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E) (a b : Fin n) :
    gramR R σ J (mulTup D X) a b = (conjT R σ D * gramR R σ J X * D) a b := by

  simp only [gramR, hR, Formalism.UG.hform, mulTup, conjT, Matrix.mul_apply, Matrix.transpose_apply,
  Matrix.map_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  have h1 : ∀ f : Fin M → Fin M → Fin n → Fin n → R ⊗[F] E,
      (∑ i, ∑ j, ∑ l, ∑ k, f i j l k) = ∑ l, ∑ k, ∑ i, ∑ j, f i j l k := by
    intro f
    calc _ = ∑ i, ∑ l, ∑ j, ∑ k, f i j l k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ l, ∑ i, ∑ j, ∑ k, f i j l k := Finset.sum_comm
      _ = ∑ l, ∑ i, ∑ k, ∑ j, f i j l k :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ l, ∑ k, ∑ i, ∑ j, f i j l k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  refine (h1 _).trans ?_
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gramMulTup_holds : GramMulTup := by
  intro F E _ _ _ R _ _ σ n M J D X
  ext a b
  exact gram_entry R σ n M J D X a b

end PI.NcVal.OmVc1
