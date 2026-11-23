module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTameInertiaElementAtTwistPrime
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleConjugatePairPlacesEqSelfOfGoodChars
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.admissibleConjugatePairPlaces_eq_self_of_good_chars : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (M : ℕ) (Q : Finset (Pl D.host.E)) (d : PlE D.host → (G D.host.E N.Om →* Multiplicative (ZMod (X.l i ^ M)))), (∀ P ∈ Q, IsSplitPl D.host P) → (∀ P ∈ Q, ∀ P', IsConjPl D.host P P' → P' ∈ Q) → (∀ P ∈ Q, GlobalTheory.TwSys.GoodChar X i M P (d P) ∧ normV P % (2 * X.l i ^ M) = 1) → (0 < M ∨ ∀ P ∈ Q, P ∉ placesOver D.host.E (X.l i)) → admissibleConjugatePairPlaces X i Q M = Q := by
  first | exact @GlobalTheory.AdmSelf.admissibleConjugatePairPlaces_eq_self_of_goodChar | exact GlobalTheory.AdmSelf.admissibleConjugatePairPlaces_eq_self_of_goodChar | (intros; apply GlobalTheory.AdmSelf.admissibleConjugatePairPlaces_eq_self_of_goodChar <;> assumption)
