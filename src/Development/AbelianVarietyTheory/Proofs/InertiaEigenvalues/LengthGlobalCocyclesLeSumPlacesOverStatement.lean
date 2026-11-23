module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LenCob
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthGlobalCocyclesLeSumPlacesOver
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

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

theorem _root_.GlobalTheory.T.length_global_cocycles_le_sum_places_over : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k)) (e : ℕ), (∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), LocBound i w hw r Xs M e ∧ ∀ f ∈ C, InCut i r Xs M w hw f) → ∃ C' : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k), C' ≤ C ∧ (∀ f ∈ C', IsFinL i M f) ∧ Module.length (D.nd.O i) ↥C ≤ (((placesOver D.host.E (D.nd.l i)).ncard * e : ℕ) : ℕ∞) * lenQ i ((D.nd.l i : ℕ) : D.nd.O i) + Module.length (D.nd.O i) ↥C' := by
  first | exact @GlobalTheory.Cut.CountL.main | exact GlobalTheory.Cut.CountL.main | (intros; apply GlobalTheory.Cut.CountL.main <;> assumption)
