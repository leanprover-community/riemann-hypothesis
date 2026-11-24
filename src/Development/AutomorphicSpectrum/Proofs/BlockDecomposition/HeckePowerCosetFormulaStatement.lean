module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPermWOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckePowerCosetFormula
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.IsStrictDom

@[expose] public section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

theorem _root_.GlobalTheory.T.hecke_power_coset_formula : ∀ (G : Type) [Group G] (K I : Subgroup G), I ≤ K → Finite (K ⧸ I.subgroupOf K) → ∀ (t : G) (R : Finset G), (1 : G) ∈ R → (∀ r ∈ R, r ∈ I) → (∀ r ∈ R, ∀ k : ℕ, t ^ k * r * (t ^ k)⁻¹ ∈ K) → (∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I) → ∀ j : ℕ, ∃ m : ℕ, 0 < m ∧ ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∑ᶠ c : K ⧸ I.subgroupOf K, ((aOp R t)^[j] ψ) ((c.out : K) : G) = (m : ℂ) * hAct K (dosetInd ℂ K (t ^ j)) ψ 1 := by
  first | exact @GlobalTheory.CompanionTheory.SatPow.HeckeTrace.heckeTrace | exact GlobalTheory.CompanionTheory.SatPow.HeckeTrace.heckeTrace | (intros; apply GlobalTheory.CompanionTheory.SatPow.HeckeTrace.heckeTrace <;> assumption)
