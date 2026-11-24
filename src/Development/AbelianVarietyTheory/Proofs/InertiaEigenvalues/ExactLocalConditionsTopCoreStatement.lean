module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.AdmissibleCharUnramified
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.AdmissibleCharacterHyp
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.InvariantsVanishing
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExactLocalConditionsTopCore
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

theorem _root_.GlobalTheory.T.exactLocalConditions_topCore : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (H : LocHW l P), GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.ErrorExponentStatement P → GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses.Stmt P → GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleCharUnramified.AdmChiOneUnramified P → ∀ (K LL : FinExt l) (hA : CaseA K LL) (lam : ↥(OL LL)), Irreducible lam → tableLineDegreeTwo.TopCore (P.PD K) (H.W K 1 LL hA.2.2).emb lam (IK K) := by
  first | exact @GlobalTheory.TopDict.topCore_of_typings | exact GlobalTheory.TopDict.topCore_of_typings | (intros; apply GlobalTheory.TopDict.topCore_of_typings <;> assumption)
