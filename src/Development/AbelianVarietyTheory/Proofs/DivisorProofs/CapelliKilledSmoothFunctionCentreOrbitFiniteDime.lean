module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigencharactersFiniteOfCommutingAnnihilatedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCentreAnnihilatorCompatibleMaps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanAlgebraOrbitOfAnnihilatedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZalgEqAdjoinFiniteCapelliStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.KilledFinCentre

theorem centre_orbit_finite : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ) (q : (E →+* ℂ) → ℂ → Polynomial ℂ), (∀ τ u, q τ u ≠ 0) → ∃ (X' : Set (Module.End ℂ (Sm E b) → ℂ)) (D : ℕ), X'.Finite ∧ ∀ ψ : Sm E b, (∀ τ u, Polynomial.aeval (cap τ u) (q τ u) ψ = 0) → FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E b) => z ψ) '' Zalg E b)) ∧ Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E b) => z ψ) '' Zalg E b)) ≤ D ∧ ∀ (χ' : Module.End ℂ (Sm E b) → ℂ) (u : Sm E b), u ∈ Submodule.span ℂ ((fun z : Module.End ℂ (Sm E b) => z ψ) '' Zalg E b) → u ≠ 0 → (∀ z ∈ Zalg E b, z u = χ' z • u) → ∃ χ ∈ X', ∀ z ∈ Zalg E b, χ' z = χ z := by
  intro E _ _ _ b q hq
  classical
  obtain ⟨T, hT, hZ⟩ := GlobalTheory.T.zalg_eq_adjoin_finite_capelli E b
  let p : Module.End ℂ (Sm E b) → Polynomial ℂ := fun t =>
    if h : ∃ τ u, t = cap τ u then q h.choose h.choose_spec.choose else 1
  have hp : ∀ t ∈ T, p t ≠ 0 := by
    intro t ht
    simp only [p]
    split_ifs with h
    · exact hq _ _
    · exact one_ne_zero
  have hkill : ∀ ψ : Sm E b, (∀ τ u, Polynomial.aeval (cap τ u) (q τ u) ψ = 0) →
      ∀ t ∈ T, Polynomial.aeval t (p t) ψ = 0 := by
    intro ψ hψ t ht
    have h : ∃ τ u, t = cap τ u := hT t ht
    have key : ∀ τ u, t = cap τ u → Polynomial.aeval t (q τ u) ψ = 0 := by
      rintro τ u rfl; exact hψ τ u
    simp only [p, dif_pos h]
    exact key _ _ h.choose_spec.choose_spec
  have hc : ∀ s ∈ T, ∀ t ∈ T, Commute s t := fun s hs t ht =>
    GlobalTheory.AutGrowth.KilledFin.Zalg_commute (hZ ▸ Algebra.subset_adjoin hs) (hZ ▸ Algebra.subset_adjoin ht)
  obtain ⟨X', hX', hX'e⟩ := GlobalTheory.T.exists_mem_eigencharacters_of_eigenvector _ T p hc hp
  refine ⟨X', ∏ t ∈ T, (p t).natDegree, hX', fun ψ hψ => ?_⟩
  rw [hZ]
  obtain ⟨h1, h2⟩ := GlobalTheory.T.finiteDimensional_span_algebra_orbit_of_annihilated _ T p hc hp ψ (hkill ψ hψ)
  exact ⟨h1, h2, hX'e ψ (hkill ψ hψ)⟩

end GlobalTheory.KilledFinCentre
