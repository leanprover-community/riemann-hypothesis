module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GoodRoot
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Topology.LocallyConstant.Basic
public import Development.AutomorphicArithmetic.CommutativeAlgebra.RootsOfUnityEqLocallyConstantPowersSpectrum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Development.EtaleCohomology.EtaleSheaves.LineHigh
import Development.EtaleCohomology.EtaleSheaves.LineOneCut
import Development.EtaleCohomology.EtaleSheaves.StandardChartsLineOne

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing GlobalTheory.EtC UpperTheory.Et LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut LateralTheory.E.StandardEtaleChartsMultivariableHensel

theorem UpperTheory.scheme_roots_of_unity_eq_locallyConstant_powers :
    ∀ (X : Scheme.{0}) [IsAffine X] (q : ℕ) [NeZero q] (ζ : Γ(X, ⊤)), GoodRoot q ζ →
      (∀ g : LocallyConstant X (ZMod q), ∃ w : Γ(X, ⊤), w ^ q = 1 ∧ ∀ x : X, x ∉ X.basicOpen (w - ζ ^ (g x).val)) ∧
      (∀ w : Γ(X, ⊤), w ^ q = 1 → ∃ g : LocallyConstant X (ZMod q), ∀ x : X, x ∉ X.basicOpen (w - ζ ^ (g x).val)) ∧
      (∀ (a b : ZMod q) (x : X), x ∉ X.basicOpen (ζ ^ a.val - ζ ^ b.val) → a = b) ∧
      ∀ x : X, ∃ P : Ideal Γ(X, ⊤), ∀ f, f ∈ P ↔ x ∉ X.basicOpen f := by
  intro X _ q _ ζ hζ
  have hb : ∀ (x : X) (f : Γ(X, ⊤)), x ∉ X.basicOpen f ↔ f ∈ (X.toSpecΓ x).asIdeal := by
    intro x f
    rw [← Scheme.toSpecΓ_preimage_basicOpen]
    exact not_not
  let h := X.isoSpec.hom.homeomorph
  obtain ⟨h1, h2, h3⟩ := UpperTheory.roots_of_unity_eq_locallyConstant_powers_spectrum Γ(X, ⊤) q ζ hζ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    obtain ⟨w, hwq, hw⟩ := h1 (LocallyConstant.comap ⟨h.symm, h.symm.continuous⟩ g)
    refine ⟨w, hwq, fun x => ?_⟩
    rw [hb]
    have hx := hw (h x)
    change w - ζ ^ (g (h.symm (h x))).val ∈ (h x).asIdeal at hx
    rw [h.symm_apply_apply] at hx
    exact hx
  · intro w hw
    obtain ⟨g, hg⟩ := h2 w hw
    refine ⟨LocallyConstant.comap ⟨h, h.continuous⟩ g, fun x => ?_⟩
    rw [hb]
    exact hg (h x)
  · intro a b x hx
    rw [hb] at hx
    exact h3 a b _ hx
  · intro x
    exact ⟨(X.toSpecΓ x).asIdeal, fun f => (hb x f).symm⟩

end
