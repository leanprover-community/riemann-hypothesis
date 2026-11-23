module

public import Formalism.GaloisCohomology.StatementLoc
public import Mathlib.Topology.LocallyConstant.Basic
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
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.RingTheory.RootsOfUnity.Minpoly

@[expose] public section

open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

theorem cyclotomic_isLocallyConstant_mod {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O]
    (ε : Formalism.GaloisCohomology.GK p K →* Oˣ) (hε : ∀ (g : Formalism.GaloisCohomology.GK p K) (n : ℕ) (ζ : PadicAlgCl p), ζ ^ (p ^ n) = 1 →
      ∃ a : ℕ, g ζ = ζ ^ a ∧ (((ε) g : Oˣ) : O) - (a : O) ∈ Ideal.span {(p : O) ^ n}) (N : ℕ) :
    IsLocallyConstant (fun σ : Formalism.GaloisCohomology.GK p K => Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε σ : Oˣ) : O)) := by
  have hp : p.Prime := Fact.out
  have hne : ((p ^ N : ℕ) : PadicAlgCl p) ≠ 0 := by exact_mod_cast pow_ne_zero N hp.ne_zero
  haveI : NeZero ((p ^ N : ℕ) : PadicAlgCl p) := ⟨hne⟩
  haveI : NeZero (p ^ N) := ⟨pow_ne_zero N hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) (p ^ N)
  have hint : IsIntegral K ζ := (hζ.isIntegral (pow_pos hp.pos N)).tower_top
  haveI : FiniteDimensional K (IntermediateField.adjoin K {ζ}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hU : IsOpen ((IntermediateField.adjoin K {ζ}).fixingSubgroup : Set (Formalism.GaloisCohomology.GK p K)) :=
    IntermediateField.fixingSubgroup_isOpen _
  have key : ∀ σ τ : Formalism.GaloisCohomology.GK p K, σ ζ = τ ζ →
      Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε σ : Oˣ) : O) =
      Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) ((ε τ : Oˣ) : O) := by
    intro σ τ h
    obtain ⟨a, ha, ha'⟩ := hε σ N ζ hζ.pow_eq_one
    obtain ⟨b, hb, hb'⟩ := hε τ N ζ hζ.pow_eq_one
    have hab : ζ ^ a = ζ ^ b := by rw [← ha, ← hb, h]
    have hmod : a ≡ b [MOD p ^ N] := by
      rw [hζ.eq_orderOf]
      exact (hζ.isOfFinOrder (pow_ne_zero N hp.ne_zero)).pow_eq_pow_iff_modEq.1 hab
    obtain ⟨c, hc⟩ := hmod.dvd
    have hc' : (b : O) - (a : O) = (p : O) ^ N * (c : O) := by
      have := congrArg (Int.cast : ℤ → O) hc
      push_cast at this
      exact this
    rw [Ideal.Quotient.eq]
    have e : ((ε σ : Oˣ) : O) - ((ε τ : Oˣ) : O) =
        (((ε σ : Oˣ) : O) - a) - (((ε τ : Oˣ) : O) - b) - ((b : O) - a) := by ring
    rw [e, hc']
    exact Ideal.sub_mem _ (Ideal.sub_mem _ ha' hb')
      (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  rw [IsLocallyConstant.iff_exists_open]
  intro σ
  refine ⟨(fun τ => σ⁻¹ * τ) ⁻¹' ((IntermediateField.adjoin K {ζ}).fixingSubgroup : Set (Formalism.GaloisCohomology.GK p K)),
    hU.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp
  · intro τ hτ
    apply key
    have h1 : (σ⁻¹ * τ) ζ = ζ :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ ζ (IntermediateField.mem_adjoin_simple_self K ζ)
    have h2 := congrArg σ h1
    simpa using h2

end GlobalTheory.ShapeNeg
