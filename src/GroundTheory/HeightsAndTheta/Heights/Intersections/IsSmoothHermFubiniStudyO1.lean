module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.KrullDimension.PID

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]


variable (ι) in
abbrev Family := Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ

def AllSmooth {n : ℕ} (L : Fin n → HermLine ι) : Prop := ∀ j, IsSmoothHerm (L j)

def degs {n : ℕ} (L : Fin n → HermLine ι) : Fin n → K → ℤ := fun j => (L j).a

def pots {n : ℕ} (L : Fin n → HermLine ι) : Fin n → ((Σ k, ι k) → ℂ) → ℝ :=
  fun j z => Real.log ((L j).h z)



end Objects

def Conservation.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (p : ℕ), IsArithVar P (n + 1) → AllSmooth L → p.Prime →
    ∑ V ∈ (divSupp_finite P (C (p : ℤ))).toFinset,
        (multAt (P ⊔ Ideal.span {C (p : ℤ)}) V : ℝ) * (geoNum n V (degs L) : ℝ) =
      ptsIntegral P (pots L) (fun _ => 1)

section Inhabitants

abbrev GlobalTheory (n : ℕ) : Unit → Type := fun _ => Fin n

abbrev Xb (n : ℕ) (i : Fin n) : MRing (GlobalTheory n) := X ⟨(), i⟩

theorem isArithVar_bot (n : ℕ) : IsArithVar (⊥ : Ideal (MRing (GlobalTheory (n + 1)))) (n + 1) := by
  refine ⟨⟨()⟩, ⟨Ideal.isPrime_bot, ⟨∅, by simp, by simp⟩, fun _ => ⟨0, ?_⟩⟩, ?_, ?_⟩
  · rw [Ideal.mem_bot]
    exact X_ne_zero _
  · exact Ideal.comap_bot_of_injective _ (C_injective _ _)
  · rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
      MvPolynomial.ringKrullDim_of_isNoetherianRing,
      IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
    simp
    exact add_comm _ _

theorem isMultiHomog_Xb (n : ℕ) (i : Fin n) : IsMultiHomog (Xb n i) fun _ => 1 := by
  intro m hm k
  rw [support_X] at hm
  simp only [Finset.mem_singleton] at hm
  subst hm
  cases k
  simp [Finsupp.single_apply]

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
