module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuppAtMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatVectorThreeStepsConjugatePlaces
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
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily

@[expose] public section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap


theorem _root_.GlobalTheory.T.flatVector_three_steps_conjugate_places : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (B : Base (Vc D i) (Wc D i)) (ψ : Twist D Circle), B.Good → BaseOf R i B → ψ.Good → B.admitted ψ.Q → R.xi t = B.de.chi * ψ.chi → idem (R.Q t) + cA D (idem (R.Q t)) = idem (B.de.Q ∪ ψ.Q) + cA D (idem (B.de.Q ∪ ψ.Q)) → ∃ (eg ea et : AE D) (fg hA : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg ∧ IsIdemSum ea (keepPart (R := R) t (B.de.Q ∪ ψ.Q)) ∧ IsIdemSum et (flipPart (R := R) t (B.de.Q ∪ ψ.Q)) ∧ GlobalTheory.BaseCmp.IsTypeVec R i eg fg ∧ ThAt R i ea fg (GlobalTheory.BaseCmp.flatDat R i (keepPart (R := R) t (B.de.Q ∪ ψ.Q)) (R.xiR t) ea) hA ∧ ThAt R i (cA D et) hA (GlobalTheory.BaseCmp.flatDat R i ((flipPart (R := R) t (B.de.Q ∪ ψ.Q)).image conjPl) (fun PP => B.de.locC PP * ψ.locC PP) (cA D et)) ((princ B).vecFlat ψ) := by
  first | exact @GlobalTheory.FlatThreeSteps.vecFlat_three_steps | exact GlobalTheory.FlatThreeSteps.vecFlat_three_steps | (intros; apply GlobalTheory.FlatThreeSteps.vecFlat_three_steps <;> assumption)
