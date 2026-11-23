module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReadPk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsCompatibleOtherLaterStagesOfSameChoices
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.liftsCompatible_otherLaterStages_of_sameChoices : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (F : Face a.D A) (y : Hd R) (y' : HdB b R), Same b y y' → ∀ (Φ : Type) (rep : Φ → _) (Mt : C.Tup → ℕ → Hs) (l : LfD B.O (B.embLL.comp B.OtoLL) C.Tup Φ Mt) jL (t : LfT y F rep (Mt := Mt) jL l) jL', HEq jL' jL → ∃ t' : @LfT b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) Φ ((by with_unfolding_all exact (rep :))) Mt jL' l, letI := alg b iK; HEq t'.eW t.eW ∧ HEq t'.jMt t.jMt := by
  first | exact @GlobalTheory.Mem.R3.Rw.lfT_of_same | exact GlobalTheory.Mem.R3.Rw.lfT_of_same | (intros; apply GlobalTheory.Mem.R3.Rw.lfT_of_same <;> assumption)
