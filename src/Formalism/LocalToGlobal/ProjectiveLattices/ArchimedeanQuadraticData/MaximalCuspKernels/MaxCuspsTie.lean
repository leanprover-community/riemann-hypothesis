module

public import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
import Formalism.LocalToGlobal.ProjectiveLattices.SpanRatSmulMem
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.QAt

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj.FJ

def MaxCuspsTieStatement : Prop :=
  ∀ (D : D7) (T : Core D) (j : ℕ) (cu : T.Cu j),
    WeightFamilies.dualZ D (T.Xc j cu) = (crdI 1 cu.1.2 : Set (Fin (WeightFamilies.rho D j) → D.host.E))

theorem maxCuspsTieStatement_holds : MaxCuspsTieStatement := by
  intro D T j cu
  have h1 : WeightFamilies.dualZ D (T.Xc j cu) = dualZE (XcFD 1 cu.1.2) := rfl
  rw [h1, dualZE_eq, xcFD_restrict]
  obtain ⟨ι, _, b, hb⟩ :=
    exists_basis (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) one_ne_zero cu.1.2
  rw [← hb, LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis _ (trBE_nondeg _) (trBE_symm _) b,
    hb, Submodule.coe_restrictScalars]

end Formalism.L2.Pj.QAt
