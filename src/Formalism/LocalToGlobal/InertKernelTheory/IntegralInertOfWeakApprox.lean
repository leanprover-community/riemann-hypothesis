module

public import Formalism.LocalToGlobal.InertKernelTheory.DefsMMOnb
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntWeak
public import Formalism.LocalToGlobal.InertKernelTheory.OneCopyTh1S
public import Formalism.LocalToGlobal.InertKernelTheory.StatementInt
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.AlgKleinPf
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.GlobalOrthonormalBasisFour
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntAsm
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntEasy
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntPull
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntStd
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMFour
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.OneCopyTh1SOfIsom
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ThFourIntOf
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.UnitSubstOfLoc
public import Formalism.LocalToGlobal.InertKernelTheory.IntegralInertOfWeakApproxTheta
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntTens

@[expose] public section

namespace Formalism.L2.KerInert

def WeakApproxAndOrthonormalBases : Prop := WAPlaces ∧ OneCopyOrth ∧ IsomONB

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem integral_inert_of_weakApprox (h : WeakApproxAndOrthonormalBases) : IntInert :=
  intInert_of combination_fact pairing_fact (weakApprox_of h.1) pullback_torsion pullback_fact AlgP.algebraic_fact_kernels
    power_series_linearity pairs_standard_at_p (basisInv_of_loc unit_substitution_local) tensor_matrix_units_fact
    (thFourInt_of (oneCopyLoc_of_isom h.2.2 AlgP.zero_value_algebraic) (locInv_of unit_substitution_local) four_products_from_one
      (MMOnb.globONB_of h.2.1) AlgP.zero_value_algebraic)


end Formalism.L2.KerInert
