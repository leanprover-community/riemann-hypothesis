module

public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModuleModNBasis
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField

theorem _root_.GlobalTheory.T.projective_module_mod_N_basis : ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M], Module.Finite (𝓞 E) M → Module.Projective (𝓞 E) M → ∀ (n N : ℕ), Module.finrank (𝓞 E) M = n → 0 < N → ∃ φ : (Fin n → 𝓞 E) →ₗ[𝓞 E] M, (∀ m, ∃ x b, m = φ x + N • b) ∧ ∀ x b, φ x = N • b → ∃ x', x = N • x' := by
  first | exact @GlobalTheory.CompanionTheory.ModFree.exists_free_map_mod | exact GlobalTheory.CompanionTheory.ModFree.exists_free_map_mod | (intros; apply GlobalTheory.CompanionTheory.ModFree.exists_free_map_mod <;> assumption)
