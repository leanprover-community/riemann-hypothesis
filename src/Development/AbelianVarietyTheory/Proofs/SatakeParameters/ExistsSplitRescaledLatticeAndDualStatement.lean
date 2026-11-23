module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitRescaledLatticeAndDual
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.LocMod GlobalTheory.PlaceModel ValuativeRel

theorem _root_.GlobalTheory.T.exists_split_rescaled_lattice_and_dual : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : Formalism.BasicNotions.TH.HSp D) (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ), Formalism.L2.Theta.IsStdChar D ψ (-1) → ∀ (U : AddSubgroup (Formalism.IndefR.Datum.WO S T)), IsOpen (U : Set (Formalism.IndefR.Datum.WO S T)) → ∃ c : k, c ≠ 0 ∧ ∃ L' K : AddSubgroup (Formalism.IndefR.Datum.WO S T), (∀ x : Matrix Y Y' k, (∀ i j, x i j ∈ 𝒪[k]) → p.up FS FT (c • x) ∈ L' ∧ p.up FS FT (c • x) ∈ U) ∧ (∀ t ∈ L', Formalism.IndefR.Datum.IsHalf p.e t) ∧ (∀ y ∈ K, Formalism.IndefR.Datum.IsHalf (Formalism.L2.Theta.cA D p.e) y ∧ y ∈ U) ∧ (∃ R : Finset (Formalism.IndefR.Datum.WO S T), ∀ t ∈ L', ∃ r ∈ R, ∃ x : Matrix Y Y' k, (∀ i j, x i j ∈ 𝒪[k]) ∧ t - r = p.up FS FT (c • x)) ∧ (∀ x ∈ L', ∀ y ∈ K, ψ (Formalism.IndefR.Datum.symplO S T x y) = 1) ∧ (∀ y, Formalism.IndefR.Datum.IsHalf (Formalism.L2.Theta.cA D p.e) y → (∀ x ∈ L', ψ (Formalism.IndefR.Datum.symplO S T x y) = 1) → y ∈ K) := by
  first | exact @GlobalTheory.LatChoiceSplit.exists_split_lattices | exact GlobalTheory.LatChoiceSplit.exists_split_lattices | (intros; apply GlobalTheory.LatChoiceSplit.exists_split_lattices <;> assumption)
