module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankWeightComponentEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CmPlaceOperatorPreservesTypeAveragesShape
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

theorem _root_.GlobalTheory.T.cmPlaceOperator_preserves_type_averages_shape : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.thP_ωP → ∀ (i : Fin D.R.m) (t : T) (Sb : Finset (FinPl D)) (v : FinPl D), v ∈ Sb → ∀ (h : GA D (Wc D i)), (∀ a b, idem D (.inl v) * (Formalism.L2.Theta.mt (Wc D i) h - 1) a b = (Formalism.L2.Theta.mt (Wc D i) h - 1) a b) → ∀ (c : WO (Vc D i) (Wc D i) →₀ ℂ), (∀ y ∈ c.support, IsHalf (idem D (.inl v)) y) → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), TypeIn R i t Sb f → CleanIn R i t Sb f → LikeOff R i t Sb f → TypeIn R i t (dropPl Sb v) (comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h) f)) ∧ CleanIn R i t (dropPl Sb v) (comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h) f)) ∧ LikeOff R i t Sb (comb R.ψ (Vc D i) (Wc D i) c (R.ωP i t (1, h) f)) := by
  first | exact @GlobalTheory.DownLift.GenSplit.placeOp_keep | exact GlobalTheory.DownLift.GenSplit.placeOp_keep | (intros; apply GlobalTheory.DownLift.GenSplit.placeOp_keep <;> assumption)
