module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdentificationTypeRepresentativesClasses
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.exists_identification_typeRepresentatives_classes : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (y : Hd R), ∀ (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F rep → ∃ e : Φ ≃ principalLevelFrame.FTR R.θ y.PY (R.MY 0) (fun b => levS _ (R.βY 0) (R.dat0 (R.levR F b))) (fun b => levChi _ (R.βY 0) (R.dat0 (R.levR F b))) (fun _ => R.e0), ∀ π, (principalLevelFrame.rowRepR R.θ (e π)).Iso (rep π) ∧ (∀ b, y.prtE F b (principalLevelFrame.rowRepR R.θ (e π)) = y.prtE F b (rep π)) ∧ (∀ i, y.prtW F i (principalLevelFrame.rowRepR R.θ (e π)) = y.prtW F i (rep π)) ∧ ∃ b, y.prtE F b (rep π) ≠ ⊥ ∧ y.prtE F b (rep π) ≤ (y.C F).EEc b := by
  first | exact @GlobalTheory.Mem.R3.Rw.RepCls.reps_classes | exact GlobalTheory.Mem.R3.Rw.RepCls.reps_classes | (intros; apply GlobalTheory.Mem.R3.Rw.RepCls.reps_classes <;> assumption)
