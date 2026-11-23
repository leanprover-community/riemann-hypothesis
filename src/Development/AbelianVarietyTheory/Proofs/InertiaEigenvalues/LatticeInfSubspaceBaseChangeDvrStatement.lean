module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeInfSubspaceBaseChangeDvr
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
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module

theorem _root_.GlobalTheory.T.lattice_inf_subspace_baseChange_dvr : ∀ (K : Type) [Field K] [NumberField K] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (e : K →+* FractionRing O) (V V' : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] [AddCommGroup V'] [Module (FractionRing O) V'] [Module O V'] [IsScalarTower O (FractionRing O) V'] (iV : V →ₛₗ[e] V') (ι : Type) (b : Basis ι K V), LinearIndependent (FractionRing O) (fun a => iV (b a)) → (∀ a : 𝓞 K, e (a : K) ∈ (algebraMap O (FractionRing O)).range) → ∀ (A : Submodule (𝓞 K) V) (U : Submodule K V), Submodule.span O (iV '' ((A ⊓ U.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V)) = Submodule.span O (iV '' (A : Set V)) ⊓ (Submodule.span (FractionRing O) (iV '' (U : Set V))).restrictScalars O := by
  first | exact @GlobalTheory.LatticeInterBaseChange.span_inf_baseChange | exact GlobalTheory.LatticeInterBaseChange.span_inf_baseChange | (intros; apply GlobalTheory.LatticeInterBaseChange.span_inf_baseChange <;> assumption)
