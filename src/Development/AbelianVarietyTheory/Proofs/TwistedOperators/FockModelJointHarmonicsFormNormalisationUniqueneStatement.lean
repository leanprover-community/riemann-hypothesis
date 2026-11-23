module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockModelJointHarmonicsFormNormalisationUniquene
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

theorem _root_.GlobalTheory.T.fockModel_jointHarmonics_form_normalisation_uniqueness : ∀ (X : ProvA) (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ), (∀ Φ, CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ ↔ Φ ∈ (X.fock p q r s).J ∧ IsHW (fockAct1 p q r s) μ Φ ∧ IsHW (fockAct2 p q r s) μ' Φ) ∧ (∀ Φ, CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ → ∃ c : ℝ, 0 < c ∧ JointHW (X.fock p q r s) μ μ' ((c : ℂ) • Φ)) ∧ ∀ Φ Φ', CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ → CJoint (fockAct1 p q r s) (fockAct2 p q r s) μ μ' Φ' → ∃ c : ℂ, Φ' = c • Φ := by
  first | exact @GlobalTheory.ArchRec.Joint.joint_harmonics | exact GlobalTheory.ArchRec.Joint.joint_harmonics | (intros; apply GlobalTheory.ArchRec.Joint.joint_harmonics <;> assumption)
