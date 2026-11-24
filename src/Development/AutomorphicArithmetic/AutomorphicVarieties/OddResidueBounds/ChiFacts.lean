module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Parity
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primmem
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.CoefMapSingle

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.chiFacts :
    ∀ (E : Type) [Field E] [NumberField E] (N : ℕ) [NeZero N] (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)), Function.Surjective ρ → ∀ (l : ℕ) [Fact l.Prime] (O : Subalgebra ℤ_[l] (PadicAlgCl l)), Function.Injective (fun ψ : (E ≃ₐ[ℚ] E) →* Oˣ => chiOf ρ ψ) ∧ ∀ (ψ : (E ≃ₐ[ℚ] E) →* Oˣ) (k : ℕ), (chiOf ρ ψ (-1) = (-1) ^ k → chiOf ρ ψ ∈ charSet (PadicAlgCl l) (parE ρ k)) ∧ ∃ a : O, (a : PadicAlgCl l) = alN k (chiOf ρ ψ) := by
  intro E _ _ N _ ρ hρ l _ O
  refine ⟨fun ψ ψ' h => ?_, fun ψ k => ⟨fun hk => ?_, ?_⟩⟩
  · refine MonoidHom.ext fun g => ?_
    obtain ⟨b, rfl⟩ := hρ g
    have hb := congrArg (fun χ : DirichletCharacter (PadicAlgCl l) N => χ (b : ZMod N)) h
    simp only [chiOf_unit] at hb
    exact Units.ext (Subtype.ext hb)
  · simp only [charSet, parE, Set.mem_setOf_eq, Set.mem_inter_iff]
    refine ⟨?_, (b_parity k _).1.2 hk⟩
    intro b hb
    rw [MonoidHom.mem_ker] at hb ⊢
    apply Units.ext
    rw [MulChar.coe_toUnitHom, chiOf_unit, hb]
    simp
  · have h := (b_primmem k (chiOf ρ ψ)).2.1 O.toSubring (fun u => by
      rw [chiOf_unit]
      exact (ψ (ρ u) : O).2)
    exact ⟨⟨_, h⟩, rfl⟩
