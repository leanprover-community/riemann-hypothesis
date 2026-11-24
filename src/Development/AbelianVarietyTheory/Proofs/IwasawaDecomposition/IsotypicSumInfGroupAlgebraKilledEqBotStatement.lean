module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotypicSumInfGroupAlgebraKilledEqBot
import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

theorem _root_.GlobalTheory.T.isotypicSum_inf_groupAlgebraKilled_eq_bot : ∀ (H S0 X : Type) [Group H] [AddCommGroup S0] [Module ℂ S0] [AddCommGroup X] [Module ℂ X] (σ0 : Representation ℂ H S0) (ρ : Representation ℂ H X) (C : Submodule ℂ X) (I : Set (MonoidAlgebra ℂ H)), σ0.IsIrreducible → killed σ0 I = ⊥ → ((⨆ f ∈ homInto σ0 ρ C, LinearMap.range f) ⊓ killed ρ I : Submodule ℂ X) = ⊥ := by
  first | exact @GlobalTheory.RepCount.iSup_range_homInto_inf_killed_eq_bot | exact GlobalTheory.RepCount.iSup_range_homInto_inf_killed_eq_bot | (intros; apply GlobalTheory.RepCount.iSup_range_homInto_inf_killed_eq_bot <;> assumption)
