module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
public import Formalism.SharpRestriction.LevelLetterCocycles.CongruenceSingleEndomorphism
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CutCongruenceValEqHeckeValueIdealOffSupportVal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem _root_.GlobalTheory.T.cutCongruenceVal_eq_heckeValueIdealOffSupportVal : ∀ (D : D7) (i : D.nd.Loc) (Xs : Set (D.nd.X i)) (π : D.nd.X i), PairedCharacterCondition.CongruenceModules.vccCut i Xs π = GlobalTheory.Cut.vccOff i Xs π := by
  first | exact @GlobalTheory.Pass.CutEq.main | exact GlobalTheory.Pass.CutEq.main | (intros; apply GlobalTheory.Pass.CutEq.main <;> assumption)
