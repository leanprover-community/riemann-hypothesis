module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis

@[expose] public section

open GlobalTheory.ExpFrame Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.FrameQuot

theorem finite_quot_prime (l : ℕ) [Fact l.Prime] (ι : Type) (N : ℕ) (F : Frame l ι N) (hF : F.Ok) :
    Finite (F.O ⧸ Ideal.span {((l : ℕ) : F.O)}) := by
  obtain ⟨hinj, L, hL, hrange⟩ := hF.ring
  haveI := hL
  have hmem : ∀ x : F.O, F.emb x ∈ L ∧ ‖F.emb x‖ ≤ 1 := fun x => by
    have hx : F.emb x ∈ Set.range F.emb := ⟨x, rfl⟩
    rw [hrange] at hx
    exact hx
  let f : F.O →+* integralClosure ℤ_[l] L :=
    { toFun := fun x => ⟨⟨F.emb x, (hmem x).1⟩,
        (GlobalTheory.mem_integralClosure_padicInt_iff L ⟨F.emb x, (hmem x).1⟩).2 (hmem x).2⟩
      map_one' := Subtype.ext (Subtype.ext (map_one F.emb))
      map_mul' := fun x y => Subtype.ext (Subtype.ext (map_mul F.emb x y))
      map_zero' := Subtype.ext (Subtype.ext (map_zero F.emb))
      map_add' := fun x y => Subtype.ext (Subtype.ext (map_add F.emb x y)) }
  have hsurj : Function.Surjective f := by
    rintro ⟨⟨y, hyL⟩, hy⟩
    have hn := (GlobalTheory.mem_integralClosure_padicInt_iff L ⟨y, hyL⟩).1 hy
    have hy' : y ∈ Set.range F.emb := by
      rw [hrange]
      exact ⟨hyL, hn⟩
    obtain ⟨x, rfl⟩ := hy'
    exact ⟨x, rfl⟩
  have hbij : Function.Bijective f :=
    ⟨fun x y h => hinj (congrArg (fun z : integralClosure ℤ_[l] L => ((z : L) : PadicAlgCl l)) h), hsurj⟩
  let e := RingEquiv.ofBijective f hbij
  have hfin : Finite (integralClosure ℤ_[l] L ⧸
      Ideal.span {((l : ℕ) : integralClosure ℤ_[l] L) ^ 1}) :=
    GlobalTheory.LocalIntegers.finite_quotient_pow l (integralClosure ℤ_[l] L) 1
  have hIJ : Ideal.span {((l : ℕ) : integralClosure ℤ_[l] L) ^ 1} =
      (Ideal.span {((l : ℕ) : F.O)}).map (e : F.O →+* integralClosure ℤ_[l] L) := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast, pow_one]
  exact Finite.of_equiv _ (Ideal.quotientEquiv _ _ e hIJ).symm.toEquiv

end GlobalTheory.FrameQuot
