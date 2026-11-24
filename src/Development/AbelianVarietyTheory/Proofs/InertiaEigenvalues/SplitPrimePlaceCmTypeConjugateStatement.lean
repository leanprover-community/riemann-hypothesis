module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SplitPlaceTypes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPrimePlaceCmTypeConjugate
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

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.FrobeniusOrbits GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

theorem _root_.GlobalTheory.T.splitPrime_place_cmType_conjugate : ∀ (D : D7) (i : D.nd.Loc), SplitRowPrime D.host (D.nd.l i) → ∀ (w w' : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (hw' : w' ∈ placesOver D.host.E (D.nd.l i)), IsConjPl D.host w w' → (PlIn (N := D.nd) D.nbr i true w hw ∧ PlIn (N := D.nd) D.nbr i false w' hw') ∨ (PlIn (N := D.nd) D.nbr i false w hw ∧ PlIn (N := D.nd) D.nbr i true w' hw') := by
  first | exact @GlobalTheory.SplitType.place_type_conj | exact GlobalTheory.SplitType.place_type_conj | (intros; apply GlobalTheory.SplitType.place_type_conj <;> assumption)
