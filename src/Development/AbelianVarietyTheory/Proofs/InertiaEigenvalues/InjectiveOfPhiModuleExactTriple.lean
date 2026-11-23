module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TameDescentExtendedActionExtraVector
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulVecEqZeroOfSubalgebra
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

open PowerSeries GlobalTheory.BK

open Matrix

namespace GlobalTheory.BK

theorem mulVec_eq_zero_of_subalgebra {O S : Type} [CommRing O] [CommRing S] [IsDomain S] [Algebra O S]
    (B : Subalgebra O S) {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix κ ι S) (hM : ∀ i j, M i j ∈ B)
    (hinj : ∀ v : ι → S, (∀ j, v j ∈ B) → M *ᵥ v = 0 → v = 0) (w : ι → S) (hw : M *ᵥ w = 0) :
    w = 0 := by
  first
  | (rename_i h_2 h_3 h_4 h_5 h_9 h_10 h_11 h_12; revert O S h_2 h_3 h_4 h_5 B ι κ h_9 h_10 h_11 h_12 M hM hinj w hw; exact @_root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra)
  | exact @_root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra
  | exact _root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra
  | (apply _root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra <;> assumption)
  | (intros; apply _root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra ..)

end GlobalTheory.BK

theorem GlobalTheory.BK.IsExactTriple.injective_app : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] (ι κ μ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (T : PhiMod O K l e a μ) (F : Hom P Q) (G : Hom Q T), IsExactTriple F G → Function.Injective F.app := by
  intro O K _ _ _ _ _ l e a _ ι κ μ _ _ _ _ _ _ P Q T F G hex
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  funext τ
  refine mulVec_eq_zero_of_subalgebra (A O K) (F.mat τ) (F.mem τ) ?_ (w τ) ?_
  · intro v hv hMv
    have hu : Pi.single τ v ∈ P.M := mem_tot.2 fun τ' => by
      by_cases h : τ' = τ
      · subst h; simpa using (mem_vecs.2 hv)
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _
    have h0 : F.app (Pi.single τ v) = 0 := by
      funext τ'
      rw [Hom.app_apply]
      by_cases h : τ' = τ
      · subst h; simpa using hMv
      · rw [Pi.single_eq_of_ne h, Matrix.mulVec_zero]; rfl
    have := congrFun (hex.inj _ hu h0) τ
    simpa using this
  · have := congrFun hw τ
    rwa [Hom.app_apply] at this
