module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualModuleConjugateEigenAction
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigCoordApply

@[expose] public section

open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

theorem _root_.GlobalTheory.T.dual_module_conjugate_eigen_action : ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [Fintype (E →+* C)] (bar : 𝓞 E ≃+* 𝓞 E) (s s' : E →+* C) (W : Type) [AddCommGroup W] [Module C W] [FiniteDimensional C W] (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W)), (∀ y, ∑ t, HT.eigProj ρ t y = y) → (∀ a : 𝓞 E, s' (a : E) = s (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → Module.finrank C ↥(HT.eigSp ρH s ⊓ LinearMap.ker (LinearMap.fst C W (Module.Dual C W))) = Module.finrank C (HT.eigSp ρ s') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualRank.finrank_eigSp_inf_ker_fst | exact GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualRank.finrank_eigSp_inf_ker_fst | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ExG.DualRank.finrank_eigSp_inf_ker_fst <;> assumption)
