module

public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardSublatticesQuotientProdDegreeOnePrimes
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen

@[expose] public section

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

theorem _root_.GlobalTheory.T.card_sublattices_quotient_prod_degree_one_primes : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V), Submodule.IsFullLattice K M → ∀ (T : ℕ) (s : Finset (Ideal (𝓞 K))), T.Prime → (∀ P ∈ s, P.IsMaximal ∧ Ideal.absNorm P = T) → {L : Submodule (𝓞 K) V | L ≤ M ∧ Nonempty ((↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ ∏ P ∈ s, P))}.encard = (((∑ i ∈ Finset.range (Module.finrank K V), T ^ i) ^ s.card : ℕ) : ℕ∞) := by
  first
  | exact @GlobalTheory.SublatCount.main
  | intro K V _ _ _ _ _ _ _ M hM T s hT hs
    exact GlobalTheory.SublatCount.main K V M hM.toIsLattice T s hT hs
