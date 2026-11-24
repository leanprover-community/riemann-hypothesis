module

public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceDoubleCosetOperatorSemisimpleTypeSpace
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.NumberFieldFamilies.NPartCBase
import Formalism.LocalToGlobal.NumberFieldFamilies.NPartCNd
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

theorem _root_.GlobalTheory.T.splitPlace_doubleCosetOperator_semisimple_typeSpace : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))), (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → NG.HypOutside J χ B → ∀ (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ), s.v ∉ B → IsUnif L s.v ϖ → 1 ≤ k → k ≤ n → ∀ f ∈ NG.TypeSp a.ρ J χ, ∀ μ : ℂ, NG.tN J s ϖ k (NG.tN J s ϖ k f - μ • f) = μ • (NG.tN J s ϖ k f - μ • f) → NG.tN J s ϖ k f = μ • f := by
  first | exact @GlobalTheory.HeckeNormal.tN_semisimple | exact GlobalTheory.HeckeNormal.tN_semisimple | (intros; apply GlobalTheory.HeckeNormal.tN_semisimple <;> assumption)
