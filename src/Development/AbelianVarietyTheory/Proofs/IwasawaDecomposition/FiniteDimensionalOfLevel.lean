module

public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

namespace GlobalTheory.LevelForms

theorem finiteDimensional_of_level : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ρ : Representation ℂ (GQ L n) W) (N : ℕ), 0 < N →
    ∀ S : Submodule ℂ (GAf L n → W), (∀ f ∈ S, f ∈ NG.AFall L n ρ ∧ ∀ κ, NG.Cong L n N κ → NG.rt L n κ f = f) →
    FiniteDimensional ℂ S := by
  intro L _ _ _ n W _ _ _ ρ N hN S hS
  haveI := GlobalTheory.AlgFormsFin.fixedForms_finite L n ρ (GlobalTheory.T.finite_doubleCosets_definiteUnitary_maximalLevel L n) hN
  refine Submodule.finiteDimensional_of_le (S₂ := GlobalTheory.AlgFormsFin.fixedForms L n ρ N) fun f hf => ?_
  exact ⟨(hS f hf).1.1, fun κ hκ g => congrFun ((hS f hf).2 κ hκ) g⟩

end GlobalTheory.LevelForms
