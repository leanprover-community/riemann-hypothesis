module

public import Formalism.SatakeDualWeyl.StatementC
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

noncomputable section

open Matrix NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.G

section Places

variable (F : Type) [Field F] [NumberField F]

theorem finite_placesOver (g : ℕ) (hg : g ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | ((g : ℕ) : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((g : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hg
  refine (Ideal.finite_factors h0).subset ?_
  intro v hv
  exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hv)


open Classical in
def placesOver (g : ℕ) : Finset (HeightOneSpectrum (𝓞 F)) := by
  classical
  exact if h : {v : HeightOneSpectrum (𝓞 F) | ((g : ℕ) : 𝓞 F) ∈ v.asIdeal}.Finite then
    h.toFinset else ∅

theorem mem_placesOver (g : ℕ) (hg : g ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    v ∈ placesOver F g ↔ ((g : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  rw [placesOver, dite_eq_left (finite_placesOver F g hg)]
  simp

end Places

section Prod

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

def prodChar {Z : Type} [CommGroup Z] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F)))
    (lam : ∀ v, v ∈ S → (Uloc v →* Z)) (Up : Subgroup (GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (h : ∀ v ∈ S, Up ≤ (Uloc v).comap (bc (prV (E := E) v))) : Up →* Z :=
  ∏ v ∈ S.attach, (lam v.1 v.2).comp
    (((bc (prV (E := E) v.1)).subgroupComap (Uloc v.1)).comp (Subgroup.inclusion (h v.1 v.2)))

end Prod

end Formalism.L2.G
