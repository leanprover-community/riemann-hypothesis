module

public import Development.EtaleCohomology.EtaleSheaves.StrictLocalStalks
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

open CategoryTheory Limits LateralTheory.E.t_E3Cut

namespace LateralTheory.E.ULAStalkPf

theorem polyPO : PolyPO := by
  intro A B b
  let _ : Algebra A B := b.hom.toAlgebra
  let _ : Algebra (Polynomial A) (Polynomial B) := (Polynomial.mapRingHom b.hom).toAlgebra
  have _ : IsScalarTower A (Polynomial A) (Polynomial B) := IsScalarTower.of_algebraMap_eq (fun a => by
    change Polynomial.C (b.hom a) = Polynomial.map b.hom (Polynomial.C a)
    rw [Polynomial.map_C])
  have hP : Algebra.IsPushout A B (Polynomial A) (Polynomial B) := by
    refine ⟨IsBaseChange.of_equiv (polyEquivTensor' A B).symm.toLinearEquiv (fun p => ?_)⟩
    change (polyEquivTensor A B).symm (1 ⊗ₜ p) = Polynomial.map b.hom p
    rw [polyEquivTensor_symm_apply_tmul_eq_smul, one_smul]; rfl
  exact CommRingCat.isPushout_iff_isPushout.mpr hP.symm

end LateralTheory.E.ULAStalkPf
