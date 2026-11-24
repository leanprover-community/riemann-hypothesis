module

public import Formalism.AlgebraicWeights.IsAlgWeight
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L), (∀ g : GAf L n, ∃ x y : GAf L n, TrivOutside {s.v} x ∧ TrivOutside {s.v}ᶜ y ∧ g = x * y) ∧ (∀ x y : GAf L n, TrivOutside {s.v} x → TrivOutside {s.v}ᶜ y → Commute x y) ∧ (∀ A : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)), ∃! x : GAf L n, TrivOutside {s.v} x ∧ s.loc n x = A) := by
  first | exact @GlobalTheory.SplitAdelic.main | exact GlobalTheory.SplitAdelic.main | (intros; apply GlobalTheory.SplitAdelic.main <;> assumption)
