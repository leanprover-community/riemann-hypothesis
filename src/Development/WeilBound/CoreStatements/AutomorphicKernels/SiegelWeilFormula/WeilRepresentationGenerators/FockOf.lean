module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.JnArcFin
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.IntSch
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.FockLatticeInjective
import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeilRepresentationGenerators.HgSch, Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeilRepresentationGenerators.MulCoordMem, Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeilRepresentationGenerators.FockOf

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeilRepresentationGenerators.HgSch =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeilRepresentationGenerators.HgSch", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.JnArcFin\nimport Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup\nimport Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.FockLatticeInjective\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.IntSch\nimport Mathlib.Algebra.Order.Archimedean.Real.Hom\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP.OswGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

def zInv (z : InfinitePlace F → Fin d.m → Fin d.n → ℂ) : Iw d → ℝ :=
  fun i => if i.2.2.2 then (z i.1 i.2.1 i.2.2.1).re else (z i.1 i.2.1 i.2.2.1).im


variable (d) in
def zLE : (Iw d → ℝ) ≃ₗ[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ) where
  toFun := zOf (d := d)
  invFun := zInv (d := d)
  map_add' u v := by
    funext w a j
    apply Complex.ext <;> simp [zOf]
  map_smul' c u := by
    funext w a j
    apply Complex.ext <;> simp [zOf]
  left_inv u := by
    funext i
    obtain ⟨w, a, j, b⟩ := i
    cases b <;> simp [zOf, zInv]
  right_inv z := by
    funext w a j
    apply Complex.ext <;> simp [zOf, zInv]

theorem hg_sch (R : RD d) {νf : Measure (Yf d)} (hνf : νf.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM)
    {g : Yf d → ℂ} (hg' : g ∈ SB (Yf d)) : ∃ h : 𝓢(Vw d, ℂ), ⇑h = hg R νf f g := by
  obtain ⟨L, hL⟩ := KFock.archEquiv d R
  let Zc : Vw d ≃L[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ) :=
    (EuclideanSpace.equiv (Iw d) ℝ).trans (zLE d).toContinuousLinearEquiv
  let c : Vw d → Yf d → (Fin d.m × Fin d.n × Fin 2 → AF F) := fun u y k =>
    (Prod.mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (L.symm (Zc u) k)) (y k) : AF F)
  have hc1 : ∀ u y, (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (c u y k).1) = L.symm (Zc u) := by
    intro u y
    funext k
    exact RingEquiv.apply_symm_apply _ _
  have hjn : ∀ u y, jn R u y = d.cmb (c u y) := by
    intro u y
    refine (exists_jn R u y).unique ⟨arc_jn R u y, fin_jn R u y⟩ ⟨?_, ?_⟩
    · rw [arc_eq_iff]
      intro w
      rw [← hL (c u y) w, hc1, ContinuousLinearEquiv.apply_symm_apply]
      rfl
    · funext k
      show (d.crd (d.cmb (c u y)) k).2 = y k
      rw [KFock.crd_cmb']
  haveI := hνf
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI : SecondCountableTopology (Af F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : BorelSpace (Yf d) := Pi.borelSpace
  have hint : ∀ g' ∈ SB (Yf d), Integrable (fun y => g' y * star (g y)) νf := by
    intro g' hg''
    have hc : Continuous (fun y => g' y * star (g y)) :=
      hg''.1.continuous.mul (continuous_star.comp hg'.1.continuous)
    exact hc.integrable_of_hasCompactSupport (hg''.2.mul_right (f' := fun y => star (g y)))
  have key : ∀ Φ ∈ schA F (Fin d.m × Fin d.n × Fin 2), (∀ u, Integrable (fun y => Φ (c u y) * star (g y)) νf) ∧
      ∃ h : 𝓢(Vw d, ℂ), ∀ u, h u = ∫ y, Φ (c u y) * star (g y) ∂νf := by
    intro Φ hΦ
    unfold schA at hΦ
    induction hΦ using Submodule.span_induction with
    | mem Φ hmem =>
      obtain ⟨φ, g', hg'', rfl⟩ := hmem
      have e : ∀ u y, pureA F φ g' (c u y) = φ (L.symm (Zc u)) * g' y := by
        intro u y
        simp only [pureA]
        rw [hc1]
      refine ⟨fun u => ?_, ⟨(∫ y, g' y * star (g y) ∂νf) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Zc.trans L.symm) φ,
        fun u => ?_⟩⟩
      · simp only [e, mul_assoc]
        exact (hint g' hg'').const_mul _
      · simp only [e, mul_assoc, integral_const_mul, SchwartzMap.smul_apply,
          SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, ContinuousLinearEquiv.trans_apply,
          smul_eq_mul]
        ring
    | zero => exact ⟨fun u => by simp, 0, fun u => by simp⟩
    | add Φ₁ Φ₂ _ _ h₁ h₂ =>
      obtain ⟨i1, k1, e1⟩ := h₁
      obtain ⟨i2, k2, e2⟩ := h₂
      refine ⟨fun u => ?_, k1 + k2, fun u => ?_⟩
      · simp only [Pi.add_apply, add_mul]
        exact (i1 u).add (i2 u)
      · simp only [Pi.add_apply, add_mul, SchwartzMap.add_apply, e1, e2]
        rw [integral_add (i1 u) (i2 u)]
    | smul a Φ _ h =>
      obtain ⟨i1, k1, e1⟩ := h
      refine ⟨fun u => ?_, a • k1, fun u => ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
        exact (i1 u).const_mul a
      · simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, SchwartzMap.smul_apply, e1, integral_const_mul]
  obtain ⟨-, h, eh⟩ := key (f ∘ d.cmb) hf
  refine ⟨h, funext fun u => ?_⟩
  rw [eh u]
  show _ = ∫ y, f (jn R u y) * star (g y) ∂νf
  simp only [hjn, Function.comp_apply]

end PositivityTheory.SiegelWeilFormula.KFP.OswGen

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeilRepresentationGenerators.HgSch =====

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeilRepresentationGenerators.MulCoordMem =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeilRepresentationGenerators.MulCoordMem", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.JnArcFin\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP.OswGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

theorem arc_apply (R : RD d) (X : Mx F E d.m d.n) (i : Iw d) :
    arc R X i = if i.2.2.2 then (R.loc i.1 X i.2.1 i.2.2.1).re else (R.loc i.1 X i.2.1 i.2.2.1).im := rfl

theorem norm_arc_sq (R : RD d) (X : Mx F E d.m d.n) :
    ‖arc R X‖ ^ 2 = ∑ w, ∑ a, ∑ j, ‖R.loc w X a j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, arc_apply, if_true, Bool.false_eq_true, if_false,
    Real.norm_eq_abs, sq_abs]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem gauss_eq (R : RD d) (X : Mx F E d.m d.n) :
    ((Real.exp (-(2 * Real.pi * ‖arc R X‖ ^ 2)) : ℝ) : ℂ) = ∏ w, gs (2 * Real.pi) (R.loc w X) := by
  rw [Complex.ofReal_exp, norm_arc_sq]
  simp only [gs]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_neg_distrib]

def lin (a : Fin d.m) (j : Fin d.n) (b : Bool) : PX d.m d.n :=
  if b then MvPolynomial.C (1 / 2) * (MvPolynomial.X (a, j, false) + MvPolynomial.X (a, j, true))
  else MvPolynomial.C (-Complex.I / 2) * (MvPolynomial.X (a, j, false) - MvPolynomial.X (a, j, true))

theorem evX_lin (a : Fin d.m) (j : Fin d.n) (b : Bool) (z : Fin d.m → Fin d.n → ℂ) :
    evX (lin (d := d) a j b) z = ((if b then (z a j).re else (z a j).im : ℝ) : ℂ) := by
  cases b
  · simp only [lin, evX, Bool.false_eq_true, if_false, map_mul, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X,
      if_true]
    apply Complex.ext <;> simp <;> ring
  · simp only [lin, evX, if_true, Bool.false_eq_true, if_false, map_mul, map_add (f := _), MvPolynomial.eval_C,
      MvPolynomial.eval_X]
    apply Complex.ext <;> simp <;> ring

theorem fP_mul (P Q : PX d.m d.n) (u : Fin d.m → Fin d.n → ℂ) : fP (P * Q) u = evX P u * fP Q u := by
  simp only [fP, evX, map_mul]
  ring

theorem mul_coord_mem (R : RD d) (i : Iw d) {h : Mx F E d.m d.n → ℂ} (hh : h ∈ R.fock) :
    (fun X => ((arc R X i : ℝ) : ℂ) * h X) ∈ R.fock := by
  unfold RD.fock RD.fockOn at hh ⊢
  induction hh using Submodule.span_induction with
  | mem h hmem =>
    obtain ⟨P, g, hg, rfl⟩ := hmem
    apply Submodule.subset_span
    refine ⟨Function.update P i.1 (lin i.2.1 i.2.2.1 i.2.2.2 * P i.1), g, hg, ?_⟩
    funext X
    have e1 : ∏ w ∈ Finset.univ, fP (Function.update P i.1 (lin i.2.1 i.2.2.1 i.2.2.2 * P i.1) w) (R.loc w X) =
        fP (lin i.2.1 i.2.2.1 i.2.2.2 * P i.1) (R.loc i.1 X) * ∏ w ∈ Finset.univ.erase i.1, fP (P w) (R.loc w X) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i.1), Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun w hw => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]
    have e2 : ∏ w ∈ Finset.univ, fP (P w) (R.loc w X) =
        fP (P i.1) (R.loc i.1 X) * ∏ w ∈ Finset.univ.erase i.1, fP (P w) (R.loc w X) :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ i.1)).symm
    dsimp only
    rw [e1, e2, fP_mul, evX_lin, arc_apply]
    ring
  | zero =>
    convert Submodule.zero_mem _ using 1
    funext X
    simp
  | add h₁ h₂ _ _ i₁ i₂ =>
    convert Submodule.add_mem _ i₁ i₂ using 1
    funext X
    simp [mul_add]
  | smul a h _ i₁ =>
    convert Submodule.smul_mem _ a i₁ using 1
    funext X
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem poly_mem (R : RD d) (Q : MvPolynomial (Iw d) ℂ) {g : Yf d → ℂ} (hg : g ∈ SB (Yf d)) :
    (fun X => MvPolynomial.eval (fun i => ((arc R X i : ℝ) : ℂ)) Q * (Real.exp (-(2 * Real.pi * ‖arc R X‖ ^ 2)) : ℂ) *
      g (fin d X)) ∈ R.fock := by
  have base : (fun X => (Real.exp (-(2 * Real.pi * ‖arc R X‖ ^ 2)) : ℂ) * g (fin d X)) ∈ R.fock := by
    unfold RD.fock RD.fockOn
    apply Submodule.subset_span
    refine ⟨fun _ => 1, g, hg, ?_⟩
    funext X
    rw [gauss_eq]
    simp only [fP, evX, map_one, one_mul]
    rfl
  induction Q using MvPolynomial.induction_on with
  | C a =>
    convert Submodule.smul_mem _ a base using 1
    funext X
    simp only [MvPolynomial.eval_C, Pi.smul_apply, smul_eq_mul]
    ring
  | add p q hp hq =>
    convert Submodule.add_mem _ hp hq using 1
    funext X
    simp only [map_add, Pi.add_apply]
    ring
  | mul_X p i hp =>
    convert mul_coord_mem R i hp using 1
    funext X
    simp only [map_mul, MvPolynomial.eval_X]
    ring

end PositivityTheory.SiegelWeilFormula.KFP.OswGen

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeilRepresentationGenerators.MulCoordMem =====

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeilRepresentationGenerators.FockOf =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeilRepresentationGenerators.FockOf", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeilRepresentationGenerators.HgSch\nimport Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup\nimport Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.FockLatticeInjective\nimport Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.IntSch\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeilRepresentationGenerators.MulCoordMem\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP.OswGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

theorem crd_inf_eq (R : RD d)
    (L : (Fin d.m × Fin d.n × Fin 2 → mixedEmbedding.mixedSpace F) ≃L[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ))
    (hL : ∀ (c : Fin d.m × Fin d.n × Fin 2 → AF F) (w : InfinitePlace F),
      L (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (c k).1) w = R.loc w (d.cmb c)) (X : Mx F E d.m d.n) :
    (fun k => InfiniteAdeleRing.ringEquiv_mixedSpace F (d.crd X k).1) =
      L.symm (((EuclideanSpace.equiv (Iw d) ℝ).trans (zLE d).toContinuousLinearEquiv) (arc R X)) := by
  apply L.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  funext w
  rw [hL, KFock.cmb_crd]
  exact (arc_eq_iff R X (arc R X)).1 rfl w

theorem indicator_mem_SB {X : Type} [TopologicalSpace X] {N : Set X} (ho : IsOpen N) (hc : IsClosed N)
    (hk : IsCompact N) : N.indicator (fun _ => (1 : ℂ)) ∈ SB X := by
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_, HasCompactSupport.intro' hk hc fun x hx => ?_⟩
  · by_cases hx : x ∈ N
    · filter_upwards [ho.mem_nhds hx] with y hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    · filter_upwards [hc.isOpen_compl.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · exact Set.indicator_of_notMem hx _

theorem mem_fock_of (R : RD d) {νf : Measure (Yf d)} (hνf : νf.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ d.schM) (H : ∀ g ∈ SB (Yf d), ∃ P : MvPolynomial (Iw d) ℂ,
      ∀ u, hg R νf f g u = MvPolynomial.eval (fun i => ((u i : ℝ) : ℂ)) P * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2))) :
    f ∈ R.fock := by
  obtain ⟨L, hL⟩ := KFock.archEquiv d R
  set Zc : Vw d ≃L[ℝ] (InfinitePlace F → Fin d.m → Fin d.n → ℂ) :=
    (EuclideanSpace.equiv (Iw d) ℝ).trans (zLE d).toContinuousLinearEquiv with hZc
  have hΦ : f ∘ d.cmb ∈ Submodule.span ℂ {Φ | ∃ (φ : SchwartzMap (Fin d.m × Fin d.n × Fin 2 → mixedEmbedding.mixedSpace F) ℂ)
      (g : (Fin d.m × Fin d.n × Fin 2 → FiniteAdeleRing (𝓞 F) F) → ℂ),
      g ∈ SB (Fin d.m × Fin d.n × Fin 2 → FiniteAdeleRing (𝓞 F) F) ∧ Φ = pureA F φ g} := hf
  obtain ⟨N, a, x, hx⟩ := Submodule.mem_span_set'.1 hΦ
  choose φ gg hgg hxeq using fun i => (x i).2

  have hfX : ∀ X, f X = ∑ i, a i * (φ i (L.symm (Zc (arc R X))) * gg i (fin d X)) := by
    intro X
    have e1 : f X = (f ∘ d.cmb) (d.crd X) := by simp [KFock.cmb_crd]
    rw [e1, ← hx, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, hxeq i, smul_eq_mul]
    congr 1
    simp only [pureA]
    rw [crd_inf_eq R L hL X]
    rfl
  have hfjn : ∀ u y, f (jn R u y) = ∑ i, a i * (φ i (L.symm (Zc u)) * gg i y) := by
    intro u y
    rw [hfX, arc_jn, fin_jn]

  let Φv : Yf d → (Fin N → ℂ) := fun y i => gg i y
  have hloc : IsLocallyConstant Φv := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun y => ?_
    have h := Filter.eventually_all.2 fun i => (IsLocallyConstant.iff_eventually_eq _).1 (hgg i).1 y
    filter_upwards [h] with z hz
    funext i
    exact hz i
  set K : Set (Yf d) := ⋃ i, tsupport (gg i) with hK
  have hKc : IsCompact K := isCompact_iUnion fun i => (hgg i).2
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun c : Fin N → ℂ => {y | Φv y = c}) (fun c => hloc.isOpen_fiber c)
    (fun y _ => Set.mem_iUnion.2 ⟨Φv y, rfl⟩)
  set Vals := t.filter (fun c => c ≠ 0) with hVals

  have hfib_sub : ∀ c : Fin N → ℂ, c ≠ 0 → {y | Φv y = c} ⊆ K := by
    intro c hc y hy
    by_contra hyK
    apply hc
    rw [← show Φv y = c from hy]
    funext i
    show gg i y = 0
    exact image_eq_zero_of_notMem_tsupport (f := gg i) fun h => hyK (Set.mem_iUnion.2 ⟨i, h⟩)
  haveI := hνf
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI : SecondCountableTopology (Af F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : BorelSpace (Yf d) := Pi.borelSpace

  let ψ : (Fin N → ℂ) → Vw d → ℂ := fun c u => ∑ i, a i * (φ i (L.symm (Zc u)) * c i)
  have hterm : ∀ c ∈ Vals, (fun X => ψ c (arc R X) * {y | Φv y = c}.indicator (fun _ => (1 : ℂ)) (fin d X)) ∈ R.fock := by
    intro c hc
    have hc0 : c ≠ 0 := (Finset.mem_filter.1 hc).2
    set Nc : Set (Yf d) := {y | Φv y = c} with hNc
    have hNo : IsOpen Nc := hloc.isOpen_fiber c
    have hNcl : IsClosed Nc := hloc.isClosed_fiber c
    have hNk : IsCompact Nc := hKc.of_isClosed_subset hNcl (hfib_sub c hc0)
    rcases Nc.eq_empty_or_nonempty with he | hne
    · have : (fun X => ψ c (arc R X) * Nc.indicator (fun _ => (1 : ℂ)) (fin d X)) = 0 := by
        funext X
        rw [he, Set.indicator_empty, mul_zero]
        rfl
      rw [this]
      exact Submodule.zero_mem _
    · have hSB := indicator_mem_SB hNo hNcl hNk
      obtain ⟨P, hP⟩ := H _ hSB
      have hm0 : 0 < νf.real Nc := by
        rw [measureReal_def]
        exact ENNReal.toReal_pos (hNo.measure_pos νf hne).ne' hNk.measure_lt_top.ne
      have hval : ∀ u, hg R νf f (Nc.indicator fun _ => (1 : ℂ)) u = ψ c u * (νf.real Nc : ℂ) := by
        intro u
        have e : (fun y => f (jn R u y) * star (Nc.indicator (fun _ => (1 : ℂ)) y)) =
            Nc.indicator (fun _ => ψ c u) := by
          funext y
          by_cases hy : y ∈ Nc
          · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, star_one, mul_one, hfjn]
            have hy' : ∀ i, gg i y = c i := fun i => congrFun hy i
            simp only [ψ, hy']
          · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, star_zero, mul_zero]
        show ∫ y, f (jn R u y) * star (Nc.indicator (fun _ => (1 : ℂ)) y) ∂νf = _
        rw [e, integral_indicator_const _ hNo.measurableSet, Complex.real_smul, mul_comm]
      have hψ : ∀ u, ψ c u = ((νf.real Nc)⁻¹ : ℂ) *
          (MvPolynomial.eval (fun i => ((u i : ℝ) : ℂ)) P * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2))) := by
        intro u
        rw [← hP u, hval u]
        have : (νf.real Nc : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hm0.ne'
        field_simp
      have e2 : (fun X => ψ c (arc R X) * Nc.indicator (fun _ => (1 : ℂ)) (fin d X)) =
          ((νf.real Nc)⁻¹ : ℂ) • (fun X => MvPolynomial.eval (fun i => ((arc R X i : ℝ) : ℂ)) P *
            (Real.exp (-(2 * Real.pi * ‖arc R X‖ ^ 2)) : ℂ) * Nc.indicator (fun _ => (1 : ℂ)) (fin d X)) := by
        funext X
        simp only [Pi.smul_apply, smul_eq_mul, hψ]
        ring
      rw [e2]
      exact Submodule.smul_mem _ _ (poly_mem R P hSB)

  have hsum : f = ∑ c ∈ Vals, (fun X => ψ c (arc R X) * {y | Φv y = c}.indicator (fun _ => (1 : ℂ)) (fin d X)) := by
    funext X
    rw [Finset.sum_apply, hfX]
    by_cases h0 : Φv (fin d X) = 0
    · have hz : ∀ i, gg i (fin d X) = 0 := fun i => congrFun h0 i
      simp only [hz, mul_zero, Finset.sum_const_zero]
      refine (Finset.sum_eq_zero fun c hc => ?_).symm
      have hc0 : c ≠ 0 := (Finset.mem_filter.1 hc).2
      have : fin d X ∉ {y | Φv y = c} := fun h => hc0 (h.symm.trans h0)
      rw [Set.indicator_of_notMem this, mul_zero]
    · have hmemK : fin d X ∈ K := hfib_sub _ h0 rfl
      have hmemt : Φv (fin d X) ∈ t := by
        have := ht hmemK
        simp only [Set.mem_iUnion, Set.mem_setOf_eq] at this
        obtain ⟨c, hct, hc⟩ := this
        rw [hc]
        exact hct
      have hmemV : Φv (fin d X) ∈ Vals := Finset.mem_filter.2 ⟨hmemt, h0⟩
      rw [Finset.sum_eq_single_of_mem _ hmemV]
      · rw [Set.indicator_of_mem (show fin d X ∈ {y | Φv y = Φv (fin d X)} from rfl), mul_one]
      · intro c _ hne
        have : fin d X ∉ {y | Φv y = c} := fun h => hne h.symm
        rw [Set.indicator_of_notMem this, mul_zero]
  rw [hsum]
  exact Submodule.sum_mem _ hterm

end PositivityTheory.SiegelWeilFormula.KFP.OswGen

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeilRepresentationGenerators.FockOf =====
