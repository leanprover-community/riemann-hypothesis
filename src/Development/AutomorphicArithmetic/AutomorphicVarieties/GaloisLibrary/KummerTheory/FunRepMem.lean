module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.funRepMem :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (N : ℕ) (U : Subgroup (G F Ω)) [U.Normal] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M],
    (∀ g, ∀ φ ∈ XDual N U R M, funRep (R := R) (M := M) U g φ ∈ XDual N U R M) ∧
    (∀ g ∈ U, ∀ φ ∈ XDual N U R M, funRep (R := R) (M := M) U g φ = φ) ∧
    ∀ (ρ : Representation R (G F Ω) M) (φ : U → M), φ ∈ EqHom N U ρ ↔
      φ ∈ XDual N U R M ∧ ∀ g u, ρ g (funRep (R := R) (M := M) U g φ u) = φ u := by
  intro F Ω _ _ _ _ _ N U _ R M _ _ _
  have hf : ∀ (g : G F Ω) (φ : U → M) (u : U),
      funRep (R := R) (M := M) U g φ u = φ (UpperTheory.V.Base.conjHom U g u) := fun _ _ _ => rfl
  have hc : ∀ (g : G F Ω) (u : U), (UpperTheory.V.Base.conjHom U g u).1 = g⁻¹ * u.1 * g := fun _ _ => rfl
  refine ⟨fun g φ hφ => ?_, fun g hg φ hφ => ?_, fun ρ φ => ?_⟩
  · have h : IsLift (RingEquiv.refl F) g.toRingEquiv := fun x => g.commutes x
    have e1 : ∀ x : G F Ω, conjGal h x = g⁻¹ * x * g := fun _ => rfl
    have hA : ∀ (A : ValuationSubring Ω) x, g.toRingEquiv x ∈ A ↔ x ∈ A.comap g.toRingEquiv.toRingHom :=
      fun _ _ => Iff.rfl
    obtain ⟨h1, h2, h3, h4⟩ := hφ
    refine ⟨h1.comp_continuous (continuous_conjHom U g), fun a b => ?_, fun A u hu => ?_, fun A hN u hu => ?_⟩
    · rw [hf, hf, hf, map_mul, h2]
    · rw [hf]
      refine h3 (A.comap g.toRingEquiv.toRingHom) _ ?_
      rw [hc, ← e1]
      exact conjGal_mem_Ine h (hA A) hu
    · rw [hf]
      refine h4 (A.comap g.toRingEquiv.toRingHom) ?_ _ ?_
      · rw [← val_lt_one (hA A), map_natCast]
        exact hN
      · rw [hc, ← e1]
        exact conjGal_mem_Dec h (hA A) hu
  · funext u
    have e : (⟨g, hg⟩ : U) * UpperTheory.V.Base.conjHom U g u = u * ⟨g, hg⟩ :=
      Subtype.ext (by simp [hc, mul_assoc])
    have e2 := congrArg φ e
    rw [hφ.2.1, hφ.2.1, add_comm] at e2
    rw [hf]
    exact add_right_cancel e2
  · unfold EqHom
    rw [Submodule.mem_inf, Submodule.mem_iInf]
    refine and_congr_right fun _ => forall_congr' fun g => ⟨fun h u => ?_, fun h u u' hu => ?_⟩
    · rw [hf]
      refine (h _ u fun x => ?_).symm
      show u.1 (g x) = g (g.symm (u.1 (g x)))
      rw [g.apply_symm_apply]
    · have e : UpperTheory.V.Base.conjHom U g u' = u := Subtype.ext (AlgEquiv.ext fun x => by
        show g.symm (u'.1 (g x)) = u.1 x
        exact g.symm_apply_eq.2 (hu x))
      rw [← h u', hf, e]
