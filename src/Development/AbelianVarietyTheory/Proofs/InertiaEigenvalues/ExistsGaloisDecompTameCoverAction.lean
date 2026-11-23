module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoversTameOfFrobeniusTeichmullerStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisActionCyclotomicPowerStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisQlEqGaloisKPrimeMulGaloisKinftyStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KummerMemFqOfMemGKinfStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.TameCoverGen

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e]
    (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
    [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : BKGal.Gl l),
    ∃ h k : BKGal.Gl l, g = h * k ∧ BKGal.sQ l h ∈ GK (ϖ.field a) ∧
      ∃ γ : BK.TameGal K l e a, BKGal.Covers K t ϖ (BKGal.sQ l k) γ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ g
  have he : e + 1 = l ^ a := TameDescentExponentData.succ_eq (K := K)
  obtain ⟨h, hh, k, hk, hg⟩ :=
    GlobalTheory.T.galoisQl_eq_galoisKPrime_mul_galoisKinfty l a e ϖ he (BKGal.sQ l g)
  let h' : BKGal.Gl l :=
    ⟨h, GK_le (K := Formalism.MainNotions.ElementDenominator.qlExt l) (K' := ϖ.field a) bot_le hh⟩
  refine ⟨h', h'⁻¹ * g, by rw [mul_inv_cancel_left], hh, ?_⟩
  have hk' : BKGal.sQ l (h'⁻¹ * g) = k := by
    rw [map_mul, map_inv, show BKGal.sQ l g = h * k from hg]
    change h⁻¹ * (h * k) = k
    rw [inv_mul_cancel_left]
  rw [hk']
  obtain ⟨s, hs⟩ := GlobalTheory.T.galois_action_cyclotomic_power l a k
  obtain ⟨z, hz, hkz⟩ := GlobalTheory.T.exists_root_of_unity_kummer_eq l a e ϖ he k hk
  exact GlobalTheory.T.exists_coversTame_of_frobenius_teichmuller l a e O K t ϖ k s z hz hs hkz

end GlobalTheory.TameCoverGen
