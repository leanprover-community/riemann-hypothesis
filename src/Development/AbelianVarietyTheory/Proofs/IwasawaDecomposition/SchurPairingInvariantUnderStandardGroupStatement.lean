module

public import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurPairingInvariantUnderStandardGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3


theorem _root_.GlobalTheory.T.schur_pairing_invariant_under_standard_group : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (θ : InfFam D) (M : DSModel V S) (n : ℕ) (P : principalLevelFrame.RowPsi V n) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), SchurAll D → V.SigOK → IsInfFam θ → μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → ∀ (h : Formalism.AUTREP.GAf D.host.E n), ∀ x ∈ principalLevelFrame.Minf θ P M, ∀ y ∈ principalLevelFrame.Minf θ P M, ipM M μ 𝓕 (principalLevelFrame.actM P M h x) (principalLevelFrame.actM P M h y) = ipM M μ 𝓕 x y := by
  exact @GlobalTheory.SchurPairingInvariant.ipM_actM
