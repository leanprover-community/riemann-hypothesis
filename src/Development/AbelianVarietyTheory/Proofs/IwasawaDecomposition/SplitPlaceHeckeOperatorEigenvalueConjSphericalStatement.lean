module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjSplit
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceHeckeOperatorEigenvalueConjSpherical
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.split_place_hecke_operator_eigenvalue_conj_spherical : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)), IsUnif L s.v ϖ → ∀ J : Subgroup (GAf L n),
    (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) →
    ∀ (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L))) (α : Fin n → ℂˣ),
    GlobalTheory.SmGL.HasSatake σ.ρ α →
    ∀ (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* (GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L), Continuous i →
    (∀ x : L, i ((GlobalTheory.HeckeFrob.conjSplit s).i x) = algebraMap L ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L) x) →
    ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (T : σ.V →ₗ[ℂ] (GAf L n → W)),
    GlobalTheory.HeckeFrob.IsLocMap (GlobalTheory.HeckeFrob.conjSplit s) σ i T →
    ∀ e ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SplitWeil.KO ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L) (Fin n)),
    ∀ k, 1 ≤ k → k ≤ n →
      ((normV (GlobalTheory.HeckeFrob.conjSplit s).w : ℕ) : ℂ) ^ (k * (k - 1) / 2) • NG.tN J s ϖ k (T e) =
        (GlobalTheory.HeckeFrob.twEig (GlobalTheory.HeckeFrob.conjSplit s).w α).esymm k • T e := by
  first | exact @GlobalTheory.HeckeEigConj.tN_eig | exact GlobalTheory.HeckeEigConj.tN_eig | (intros; apply GlobalTheory.HeckeEigConj.tN_eig <;> assumption)
