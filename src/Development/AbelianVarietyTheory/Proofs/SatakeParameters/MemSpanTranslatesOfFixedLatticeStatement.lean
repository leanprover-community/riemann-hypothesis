module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LinearIndependentWave
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemSpanTranslatesOfFixedLattice
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.LocMod GlobalTheory.PlaceModel ValuativeRel

theorem _root_.GlobalTheory.T.mem_span_translates_of_fixed_lattice : ∀ {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℂ V] (χ : G → G → ℂ), GlobalTheory.PlaceModel.IsBichar χ → ∀ (ρ : G → V →ₗ[ℂ] V) (X Yh L L' K : AddSubgroup G), L ≤ L' → L' ≤ X → K ≤ Yh → (∀ v, ρ 0 v = v) → (∀ x ∈ X, ∀ x' ∈ X, ∀ v, ρ x (ρ x' v) = ρ (x + x') v) → (∀ y ∈ Yh, ∀ y' ∈ Yh, ∀ v, ρ y (ρ y' v) = ρ (y + y') v) → (∀ x ∈ X, ∀ y ∈ Yh, ∀ v, ρ x (ρ y v) = χ x y • ρ y (ρ x v)) → (∃ R : Finset G, ∀ t ∈ L', ∃ r ∈ R, t - r ∈ L) → (∀ x ∈ L', ∀ y ∈ K, χ x y = 1) → (∀ y ∈ Yh, (∀ x ∈ L', χ x y = 1) → y ∈ K) → ∀ (W : Submodule ℂ V), (∀ v ∈ W, ∀ x ∈ X, ρ x v ∈ W) → (∀ v ∈ W, ∀ y ∈ Yh, ρ y v ∈ W) → ∀ f ∈ W, (∀ x ∈ L, ρ x f = f) → (∀ y ∈ K, ρ y f = f) → f ∈ Submodule.span ℂ {v | ∃ r ∈ X, ∃ g ∈ W, (∀ x ∈ L, ρ x g = g) ∧ (∀ y ∈ Yh, (∀ x ∈ L, χ x y = 1) → ρ y g = g) ∧ v = ρ r g} := by
  first | exact @GlobalTheory.FourierSpan.mem_span_translates_of_fixed | exact GlobalTheory.FourierSpan.mem_span_translates_of_fixed | (intros; apply GlobalTheory.FourierSpan.mem_span_translates_of_fixed <;> assumption)
