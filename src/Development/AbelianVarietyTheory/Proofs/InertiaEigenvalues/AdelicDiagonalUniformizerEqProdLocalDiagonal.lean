module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

open Matrix

namespace GlobalTheory.CellDecNat

theorem tl_eq_jsw_tl (E : Type) [Field E] [NumberField E] (n : ℕ) (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (l' : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℕ))
    (h : ∀ w i, ((l' w i : ℕ) : ℤ) = l w i) : GlobalTheory.CellDec.tl n ϖ l = GlobalTheory.JSW.tl ϖ l' := by
  classical
  unfold GlobalTheory.CellDec.tl GlobalTheory.JSW.tl
  have hm : (List.map (fun w => finGL E n (locGL E n w (GlobalTheory.JSW.diagPow (ϖ w) (l' w)))) l'.support.toList).prod =
      finGL E n (List.map (fun w => locGL E n w (GlobalTheory.JSW.diagPow (ϖ w) (l' w))) l'.support.toList).prod := by
    rw [map_list_prod, List.map_map]; rfl
  rw [hm]
  congr 1
  apply _root_.GlobalTheory.CuspRep.LocUniq.gl_ext
  intro w
  rw [map_list_prod, List.map_map,
    List.prod_map_eq_pow_single w _ (fun v hv _ => by simp only [Function.comp_apply]; exact pLoc_locGL_of_ne (Ne.symm hv) _)]
  simp only [Function.comp_apply, pLoc_locGL]
  refine Units.ext (Matrix.ext fun i j => ?_)
  have hL : ∀ i, (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l) w = ((l' w i : ℕ) : ℤ) := fun i => by
    rw [Finsupp.mapRange_apply, h]
  change pLoc E w (((GlobalTheory.SmGL.diagT (Af E) (Fin n) _ : GL (Fin n) (Af E)) : Matrix (Fin n) (Fin n) (Af E)) i j) = _
  rw [GlobalTheory.SmGL.val_diagT]
  by_cases hw : w ∈ l'.support
  · rw [List.count_eq_one_of_mem (Finset.nodup_toList _) (Finset.mem_toList.2 hw), pow_one]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      change ((ϖ w ^ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l) w : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _
      rw [hL, zpow_natCast]
      simp [GlobalTheory.JSW.diagPow]
    · simp [Matrix.diagonal_apply_ne _ hij, GlobalTheory.JSW.diagPow]
  · rw [List.count_eq_zero_of_not_mem (by simpa using hw), pow_zero]
    have h0 : l' w = 0 := by simpa using hw
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      change ((ϖ w ^ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l) w : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _
      rw [hL, h0]
      simp
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
end GlobalTheory.CellDecNat
