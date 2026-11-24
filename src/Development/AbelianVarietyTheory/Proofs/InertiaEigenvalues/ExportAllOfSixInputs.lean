module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistModuleAllCharacterPowersOfAdmissible
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.HeckeSplitOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTameInertiaElementAtTwistPrime

@[expose] public section

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

theorem GlobalTheory.exportAll_of_six_inputs :
    ∀ (D : D7) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ), admissibleIndexBoundAllPowers D.nexp (BlochKatoReduction.bk0 D) N0 → IntegralHeckeForms.IsotypicPartsInternalDirectSum D.nexp E →
      IntegralHeckeForms.GroupAlgebraIntegrality D.nexp → IntegralHeckeForms.admT4 D.nexp E → IntegralHeckeForms.TwistedSeriesSpecialisation D.nexp → IntegralHeckeForms.GoodLatticePoints D.nexp →
      ∀ i, D.ntw.NonzeroIndexPlace i → goodTwistExistsAllCoprimePowers D.nexp (BlochKatoReduction.bk0 D) E N0 i :=
  fun D E N0 h2 h3 h5 h7 h10 h11 i hi =>
    GlobalTheory.ExportFromInputs.twistModule_all_character_powers_of_admissible D.nexp (BlochKatoReduction.bk0 D) E N0 h2 h3 h5 h7 h10 h11 i hi
