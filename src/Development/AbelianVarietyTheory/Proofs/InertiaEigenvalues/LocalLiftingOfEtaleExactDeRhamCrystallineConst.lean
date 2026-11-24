module

public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleFunctorExactOnLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDdREOfIsCrys
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankIotaLetter
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.MainFinal
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.TheoremAFinal

theorem integralityFromMetric_of_le : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ CA CB CK C : ℝ, 160 ≤ C → ElementDenominator.IntegralityFromMetric D HW F Cm CA CB CK C := by
  intro D HW F Cm CA CB CK C hC
  exact Formalism.MainNotions.N.Ln34.integrality_from_metric_of_large_constant D HW F Cm CA CB CK C hC
    (fun l _ K s LL hG T₀ T₁ T₂ ι π h => GlobalTheory.LatExact.W_exact D HW F l K s LL hG T₀ T₁ T₂ ι π h)
    (GlobalTheory.CrysDdR.finrank_DdRE_of_isCrys D) (GlobalTheory.NL.IotaLetterRank.finrank_iota_letter D HW F Cm)

end GlobalTheory.TheoremAFinal
