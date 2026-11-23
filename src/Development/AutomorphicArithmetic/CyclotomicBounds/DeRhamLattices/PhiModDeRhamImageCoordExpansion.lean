module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfPowMul
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal



theorem _root_.UpperTheory.KN.phiMod_deRham_image_coord_expansion :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (α : ℕ) (hx : ∀ τ i j, E K l e ^ α * P.mx τ i j ∈ A O K) (σ : P.MMl),
    GlobalTheory.GalStep.YD t ϖ (E K l e ^ α • σ.1) = ∑ j, ϖ.iD t K (fun τ => GlobalTheory.GalStep.hatR O (coordL P (invL l (S O K e)) σ j τ : K⟦X⟧)) •
      fun i => toOD l O (ϖ.iTot t K (fun τ => ⟨E K l e ^ α * P.mx τ i j, hx τ i j⟩)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P α hx σ
  funext i
  simp only [GlobalTheory.GalStep.YD, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [← PiSys.iD_ofA, ← map_mul]

  rw [← map_sum]
  congr 1
  funext τ
  have hw' : ∀ k, (coordL P (invL l (S O K e)) σ k τ : K⟦X⟧) ∈ Rpi O K l e := fun k =>
    invL_S_le_Rpi l e (coordL P (invL l (S O K e)) σ k τ).2
  have hb' : ∀ k, E K l e ^ α * P.mx τ i k ∈ Rpi O K l e := fun k => A_le_Rpi l e (hx τ i k)
  have hs : E K l e ^ α * σ.1 τ i =
      ∑ k, (coordL P (invL l (S O K e)) σ k τ : K⟦X⟧) * (E K l e ^ α * P.mx τ i k) := by
    rw [← mx_mulVec_coordL P (invL l (S O K e)) σ τ]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hm : (∑ k, (coordL P (invL l (S O K e)) σ k τ : K⟦X⟧) * (E K l e ^ α * P.mx τ i k)) ∈ Rpi O K l e :=
    Subalgebra.sum_mem _ fun k _ => mul_mem (hw' k) (hb' k)
  have hA : ∀ k, ofA O K l e ⟨E K l e ^ α * P.mx τ i k, hx τ i k⟩ = toHat O K l e ⟨_, hb' k⟩ := fun k =>
    (toHat_eq_ofAl l e rfl).symm
  rw [hs, GlobalTheory.GalStep.hatR_of_mem (O := O) hm, Finset.sum_apply]
  simp only [Pi.mul_apply, GlobalTheory.GalStep.hatR_of_mem (O := O) (hw' _), hA, ← map_mul]

  rw [← map_sum]
  congr 1
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]
  rfl
