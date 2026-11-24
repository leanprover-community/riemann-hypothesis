module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem IsAmpleLB.of_pow_div_generated {X : Scheme.{0}} {L N : LB X} (hL : IsAmpleLB L) (hN : N.IsLB) {m : ℕ}
    (hm : 1 ≤ m) {J : Type} (u : J → (lbPow (LB.div N L) m).Sec) (hu : ⨆ i, Out.nonzeroLocus (u i) = ⊤) :
    IsAmpleLB N := by
  refine ⟨hN, hL.compactSpace, fun x => ?_⟩
  obtain ⟨n, hn, s, hs, ha⟩ := hL.exists_affine x
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hu.ge (Set.mem_univ x))
  have hD := LB.isLB_div hN hL.isLB
  obtain ⟨v, hv⟩ := exists_sec_pow_nonzeroLocus_eq_inf hL.isLB hD hN (lbIso_refl hD) (secPow s m)
    (secCast (Nat.mul_comm m n) (secPow (u i) n))
  rw [nonzeroLocus_secCast, nonzeroLocus_secPow _ hn, nonzeroLocus_secPow _ hm] at hv
  exact ⟨n * m, Nat.mul_pos hn hm, v, hv.ge ⟨hi, hs⟩,
    hv ▸ isAffineOpen_nonzeroLocus_inf (isLB_lbPow hD m) (u i) ha⟩

theorem relAmple_of_cube_div_generated : ∀ (K : Type) [Field K] (A : Over (Sp K)) (L M : LB A.left) (a r : ℕ) (u : Fin r → (lbPow (LB.div (lbPow M a) L) 3).Sec), IsProper A.hom → L.IsLB → M.IsLB → 1 ≤ a → Out.RelAmple A L → ⨆ i, Out.nonzeroLocus (u i) = ⊤ → Out.RelAmple A M := by
  intro K _ A L M a r u hA hL hM ha hamp hu
  have h₁ := (relAmple_iff_isAmpleLB_of_isAffine A hL).1 hamp
  exact (relAmple_iff_isAmpleLB_of_isAffine A hM).2 ((isAmpleLB_pow_iff hM ha).1
    (h₁.of_pow_div_generated (isLB_lbPow hM a) (by norm_num) u hu))

end GlobalTheory
