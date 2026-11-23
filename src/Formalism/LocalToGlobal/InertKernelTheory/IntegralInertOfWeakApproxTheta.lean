module

public import Formalism.LocalToGlobal.InertKernelTheory.DefsMMInv
public import Formalism.LocalToGlobal.InertKernelTheory.StatementModel
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.BeWInertOfSigma
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.EndInt
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.GenusOneDatumExistence
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.GenusOneWittExistsOf
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntUnit
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PadicNormTwoHundredSixteenEqOneOfFiveLe
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PhNorm
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SigmaAlg
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

namespace Formalism.L2.KerInert

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem genus_one_witt_exists : GenusOneWittExists := ModelP.genus_one_witt_exists_of (GenusOneDatumExistence.genus_one_datum_exists Sigma.invAlg')

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem unit_substitution_local : UnitSubstLoc :=
  unitSubstLoc_of_model (ModelP.endIntInertAll_of endomorphisms_integral_inert genus_one_witt_exists)
    (ModelP.phNormOKInertAll_of phi_norm_inert_prime endomorphisms_integral_inert genus_one_witt_exists)
    (ModelP.biaddInertAll_of (Dict.biaddInert_of (Sigma.sigmaCurveInert_of Sigma.invAlg' Sigma.secondEisensteinAlgebraic))
      genus_one_witt_exists)




end Formalism.L2.KerInert
