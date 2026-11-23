module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrrDistinctConstituentsAfterExtension
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

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.absIrr_distinct_constituents_after_extension : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GlobalTheory.SplitCoef.OSplitAt D i → GoodR D.nd i r → ∀ (K' : Type) [Field K'] (f : Kf D.nd i →+* K'), (∀ x W₁ W₂, IsIrrSub (mapRep (f.comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) W₁ → IsIrrSub (mapRep (f.comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) W₂ → W₁ ⊓ W₂ = ⊥ → ¬ IsoSub (mapRep (f.comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) W₁ W₂) → ∀ x, AbsIrrDistinct (repK D.nd i r x) := by
  first | exact @GlobalTheory.absIrrDistinct_repK_of_oSplitAt_of_mapRep_distinct | exact GlobalTheory.absIrrDistinct_repK_of_oSplitAt_of_mapRep_distinct | (intros; apply GlobalTheory.absIrrDistinct_repK_of_oSplitAt_of_mapRep_distinct <;> assumption)
