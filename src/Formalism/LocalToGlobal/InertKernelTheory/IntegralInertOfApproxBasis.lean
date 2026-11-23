module

public import Formalism.LocalToGlobal.InertKernelTheory.DefsFrONB
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntWeak
public import Formalism.LocalToGlobal.InertKernelTheory.OneCopyTh1S
public import Formalism.LocalToGlobal.InertKernelTheory.StatementInt
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.BlockFourfoldHOneEqHOne
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ConjugationFixedClosure
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.GlobalOrthonormalBasisFour
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMConj
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMIsom
public import Formalism.LocalToGlobal.InertKernelTheory.IntegralInertOfWeakApprox
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

theorem isomONB_ofLB (hLB : LocBasisMM) : IsomONB :=
  isomONB_of_facts conjugation_extension_inert hLB rational_coordinates conjugation_fixed_closure


variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem integral_inert_of_approx_basis (hWA : WAPlaces) (hLB : LocBasisMM) : IntInert :=
  integral_inert_of_weakApprox ⟨hWA, one_theta_orthonormal, isomONB_ofLB hLB⟩

end Formalism.L2.KerInert
