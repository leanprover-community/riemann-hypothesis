module

public import Formalism.LocalToGlobal.IndefiniteReal.BridgeTie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateSplitPlaceOffStableSet
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.HeckeSplitOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw Formalism.IndefR.NX
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_conjugate_splitPlace_off_stableSet : ∀ (D : D7) (S0 : Finset (PlE D.host)) (Sb : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : PlE D.host),
    (∀ P1 P2, P1 ∈ S0 → IsConjPl D.host P1 P2 → P2 ∈ S0) → placesOver D.host.E 2 ⊆ (S0 : Set (PlE D.host)) →
    (∀ Q ∈ Sb, Q ∈ S0) → IsSplitPl D.host P → P ∉ S0 →
    ∃ P' : PlE D.host, IsConjPl D.host P P' ∧ IsSplitPl D.host P' ∧ P' ∉ S0 ∧
      Formalism.IndefR.Bridge.SplitOff P (Sb : Set (Formalism.L2.DIV.Pl D.host.E)) ∧
      Formalism.IndefR.Bridge.SplitOff P' (Sb : Set (Formalism.L2.DIV.Pl D.host.E)) ∧
      ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ((2 : ℕ) : 𝓞 D.host.E) ∉ P'.asIdeal := by
  first | exact @GlobalTheory.ConjPlaceOff.exists_conj_off | exact GlobalTheory.ConjPlaceOff.exists_conj_off | (intros; apply GlobalTheory.ConjPlaceOff.exists_conj_off <;> assumption)
