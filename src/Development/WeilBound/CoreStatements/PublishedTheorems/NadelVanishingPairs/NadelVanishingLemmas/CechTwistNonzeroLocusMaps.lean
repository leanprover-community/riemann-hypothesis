module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsPowMulPowEqOfIsZeroCechH
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechTwistNonzeroLocusMaps
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory
theorem _root_.GlobalTheory.T.cech_twist_nonzero_locus_maps : ∀ (X : Scheme.{0}) (F : X.Modules) [F.IsQuasicoherent] (L : LB X), L.IsLB → ∀ (σ : L.Sec) {ι : Type} [LinearOrder ι] [Fintype ι] (U : ι → X.Opens), (∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) → ∃ (μ : ∀ (j c d : ℕ), c + j = d → (cechCube ℤ (twistZ F L c) ⊤ U ⟶ cechCube ℤ (twistZ F L d) ⊤ U)) (ρ : ∀ c : ℕ, cechCube ℤ (twistZ F L c) ⊤ U ⟶ cechCube ℤ F (nonzeroLocus σ) U), (∀ j c d h, μ j c d h ≫ ρ d = ρ c) ∧ (∀ (j j' c d e : ℕ) (h : c + j = d) (h' : d + j' = e) (h'' : c + (j + j') = e), μ j c d h ≫ μ j' d e h' = μ (j + j') c e h'') ∧ (∀ s : Finset ι, s.Nonempty → ∀ b : (cechCube ℤ F (nonzeroLocus σ) U).obj s, ∃ c : ℕ, ∃ a : (cechCube ℤ (twistZ F L c) ⊤ U).obj s, (ρ c).app s a = b) ∧ (∀ s : Finset ι, s.Nonempty → ∀ (c : ℕ) (a : (cechCube ℤ (twistZ F L c) ⊤ U).obj s), (ρ c).app s a = 0 → ∃ j, (μ j c (c + j) rfl).app s a = 0) := by
  first | exact @_root_.GlobalTheory.cechCube_nonzeroLocus_colimit | exact _root_.GlobalTheory.cechCube_nonzeroLocus_colimit | (intros; apply _root_.GlobalTheory.cechCube_nonzeroLocus_colimit <;> assumption)
