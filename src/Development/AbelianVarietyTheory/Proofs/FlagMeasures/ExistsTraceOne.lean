module

public import Formalism.HermitianLattices.StatementMass
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField

namespace GlobalTheory.TraceOnto

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem exists_star (x : 𝓞 E) : ∃ t : 𝓞 E, (t : E) = star (x : E) :=
  ⟨RingOfIntegers.mapRingHom (starRingEnd E) x, rfl⟩

def normTraceIdeal (E : Type) [Field E] [NumberField E] [StarRing E] : Ideal (𝓞 E) where
  carrier := {x | ∃ w : 𝓞 E, (w : E) + star (w : E) = (x : E) * star (x : E)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨u, hu⟩ ⟨v, hv⟩
    obtain ⟨t, ht⟩ := exists_star b
    refine ⟨u + v + a * t, ?_⟩
    push_cast
    simp only [ht, star_add, star_mul', star_star]
    linear_combination hu + hv
  smul_mem' := by
    rintro c a ⟨u, hu⟩
    obtain ⟨t, ht⟩ := exists_star c
    refine ⟨c * t * u, ?_⟩
    simp only [smul_eq_mul]
    push_cast
    simp only [ht, star_mul', star_star]
    linear_combination ((c : E) * star (c : E)) * hu

theorem exists_trace_one : ∀ (E : Type) [Field E] [NumberField E] [StarRing E],
    Formalism.HermitianLatticesTheory.IsCMUnram E → ∃ w : 𝓞 E, (w : E) + star (w : E) = 1 := by
  intro E _ _ _ h
  have htop : normTraceIdeal E = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨θ, t, ht, hn⟩ := h.2.2 P hP
    apply hn
    apply hle
    have ht' : (t : E) = star (θ : E) := ht
    refine ⟨θ * t - θ * θ, ?_⟩
    push_cast
    simp only [ht', star_sub, star_mul', star_star]
    ring
  have h1 : (1 : 𝓞 E) ∈ normTraceIdeal E := htop ▸ Submodule.mem_top
  obtain ⟨w, hw⟩ := h1
  exact ⟨w, by simpa using hw⟩

end GlobalTheory.TraceOnto
