module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoCocycleMemCoboundariesOfModUniformizerPow
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
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs

@[expose] public section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

theorem _root_.GlobalTheory.T.twoCocycle_mem_coboundaries_of_mod_uniformizer_pow : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O] {G : Type} [Group G] [TopologicalSpace G] (ε : G →* Oˣ) (ϖ : O), (∀ n : ℕ, IsOpen ((powSub (M := O) ϖ n : Submodule O O) : Set O)) → (∀ U ∈ nhds (0 : O), ∃ n : ℕ, ((powSub (M := O) ϖ n : Submodule O O) : Set O) ⊆ U) → (∀ n : ℕ, (Z1 (quotRep (twist ε O) ϖ n) : Set (G → O ⧸ powSub (M := O) ϖ n)).Finite) → ∀ (w : G × G → O), w ∈ Z2 (twist ε O) → (∀ n : ℕ, ∃ b : G → O ⧸ powSub (M := O) ϖ n, Continuous b ∧ ∀ g h : G, d1 (quotRep (twist ε O) ϖ n) b (g, h) = Submodule.Quotient.mk (w (g, h))) → w ∈ B2 (twist ε O) := by
  first | exact @GlobalTheory.PadicH2SeparatedDVR.separated_dvr_second_cohomology_mem | exact GlobalTheory.PadicH2SeparatedDVR.separated_dvr_second_cohomology_mem | (intros; apply GlobalTheory.PadicH2SeparatedDVR.separated_dvr_second_cohomology_mem <;> assumption)
