module

public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Formalism.SatakeDualWeyl.StatementC
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.HermitianLattices.StatementLat
public import Formalism.SatakeDualWeyl.DefsCS
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast

@[expose] public section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.MainNotions.Gaps.CC.Stab

open Formalism.UG Formalism.UG.CS

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

theorem exists_place_two : ∃ v : HeightOneSpectrum (𝓞 F), ((2 : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have hp : Nat.Prime 2 := Nat.prime_two
  have hpZ : Prime ((2 : ℕ) : ℤ) := Nat.prime_iff_prime_int.1 hp
  obtain ⟨Q, hQ, hov⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F)
    (Ideal.span {((2 : ℕ) : ℤ)})
  have hmem : ((2 : ℕ) : 𝓞 F) ∈ Q := by
    have : ((2 : ℕ) : ℤ) ∈ Q.under ℤ := by rw [← hov.over]; exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ.isPrime, ?_⟩, hmem⟩
  rintro rfl
  have : ((2 : ℕ) : 𝓞 F) = 0 := by simpa using hmem
  exact hp.ne_zero (by exact_mod_cast this)

instance finiteAdeleRing_nontrivial : Nontrivial (FiniteAdeleRing (𝓞 F) F) := by
  obtain ⟨v, -⟩ := exists_place_two (F := F)
  exact (evalV F v).toRingHom.domain_nontrivial

section Herm

variable [StarRing E] (σ : E →ₐ[F] E) (hσ : ∀ e, σ e = star e)
  (h : (n → E) →ₗ⋆[E] (n → E) →ₗ[E] E)







section Mass

variable (hsymm : h.IsSymm) (hpos : ∀ x : n → E, x ≠ 0 → 0 < Algebra.trace ℚ E (h x x))
  (Λ : Submodule (𝓞 E) (n → E)) (hΛ : Submodule.IsLattice E Λ)
  (hIn : ∀ g ∈ UPts σ (Formalism.UG.gram h) (FiniteAdeleRing (𝓞 F) F), globLat g Λ ∈ Formalism.HermitianLatticesTheory.genus h Λ)
  (hSurj : ∀ M ∈ Formalism.HermitianLatticesTheory.genus h Λ, ∃ g ∈ UPts σ (Formalism.UG.gram h) (FiniteAdeleRing (𝓞 F) F), globLat g Λ = M)






end Mass

end Herm

section Std

open Formalism.MainNotions.StandardLattice

variable {k : ℕ} [StarRing E] (σ : E →ₐ[F] E) (hσ : ∀ e, σ e = star e)


variable (hc : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a))





end Std

end Formalism.MainNotions.Gaps.CC.Stab
