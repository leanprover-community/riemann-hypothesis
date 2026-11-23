module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingMapLinearCombination
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CupPair
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap

@[expose] public section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.WedgeDen

theorem alternatingMap_sum_smul_eq_det_smul' {L M N : Type} [Field L] [AddCommGroup M] [Module L M]
    [AddCommGroup N] [Module L N] {n : ℕ} (f : M [⋀^Fin n]→ₗ[L] N) (g : Fin n → M)
    (a : Fin n → Fin n → L) :
    f (fun i => ∑ l, a i l • g l) = (Matrix.of a).det • f g := by
  first
  | exact @_root_.GlobalTheory.AlternatingLinearCombination.alternating_map_linear_combination
  | exact _root_.GlobalTheory.AlternatingLinearCombination.alternating_map_linear_combination
  | (apply _root_.GlobalTheory.AlternatingLinearCombination.alternating_map_linear_combination <;> assumption)
  | (intros; apply _root_.GlobalTheory.AlternatingLinearCombination.alternating_map_linear_combination <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AlternatingLinearCombination.alternating_map_linear_combination <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AlternatingLinearCombination.alternating_map_linear_combination ..)

theorem exists_smul_ιMulti_eq_smul_ιMulti : ∀ (R L M : Type) [CommRing R] [Field L] [Algebra R L] [AddCommGroup M] [Module L M] (S : Submonoid R) (n : ℕ) (g w : Fin n → M), (∀ i, ∃ r ∈ S, ∃ c : Fin n → R, algebraMap R L r • w i = ∑ l, algebraMap R L (c l) • g l) → ∃ r ∈ S, ∃ c : R, algebraMap R L r • ExteriorAlgebra.ιMulti L n w = algebraMap R L c • ExteriorAlgebra.ιMulti L n g := by
  intro R L M _ _ _ _ _ S n g w h
  classical
  choose r hr c hc using h
  refine ⟨∏ i, r i, prod_mem fun i _ => hr i, (Matrix.of c).det, ?_⟩
  rw [map_prod, ← AlternatingMap.map_smul_univ]
  simp_rw [hc]
  rw [alternatingMap_sum_smul_eq_det_smul', RingHom.map_det]
  rfl

end GlobalTheory.WedgeDen
