module

import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.Spf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.THeis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartz
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaParabolic.LRhoOm
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinOneMulEqZeroIff
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinRealAdSmulAlt
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ReduceModChar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.LrhoPf, Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.NormAddSmulSq, Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.ExpAlg

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.LrhoPf =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.LrhoPf", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.Spf\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.THeis\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartz\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaParabolic.LRhoOm\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

theorem rho_smul' (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) (c : ℂ) (φ : d.Fn) :
    d.dd.rho d.B.ψ w (c • φ) = c • d.dd.rho d.B.ψ w φ := by
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul]
  ring

theorem T_smul' (c : ℂ) (φ : d.Fn) (X : Mx F E d.m d.n) : d.T (c • φ) X = c * d.T φ X := by
  simp only [SD.T, rho_smul', map_smul, smul_eq_mul]

theorem T_rho_sum' (hH : THeis) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (Z Z' X : Mx F E d.m d.n) :
    d.T (d.dd.rho d.B.ψ (Z * (incM F d.b.1.toCols₂)ᵀ + Z' * (incM F d.b.1.toCols₁)ᵀ) Φ) X =
      d.B.ψ (-(⅟(2 : AF F) * spf d (Z * (incM F d.b.1.toCols₂)ᵀ) (Z' * (incM F d.b.1.toCols₁)ᵀ))) *
        (d.B.ψ (d.tt (d.gram Z' (X + Z))) * d.T Φ (X + Z)) := by
  have hψ : IsStd d.B.ψ := d.ok.good.std
  have hrho : ∀ w, ∀ φ ∈ d.sch, d.dd.rho d.B.ψ w φ ∈ d.sch := fun w φ hφ =>
    GlobalTheory.SchrKeepsSchA.schr_mem_schA F d.B.ψ hψ d.κ _ φ hφ
  set a := Z * (incM F d.b.1.toCols₂)ᵀ
  set b := Z' * (incM F d.b.1.toCols₁)ᵀ
  have h1 := Tpar.rho_rho (dd := d.dd) (ψ := d.B.ψ) a b Φ
  have h2 : d.dd.rho d.B.ψ (a + b) Φ =
      d.B.ψ (-(⅟(2 : AF F) * spf d a b)) • d.dd.rho d.B.ψ a (d.dd.rho d.B.ψ b Φ) := by
    have h := congrArg (fun f : d.Fn => d.B.ψ (-(⅟(2 : AF F) * spf d a b)) • f) h1
    simp only [smul_smul, ← AddChar.map_add_eq_mul, spf, neg_add_cancel,
      AddChar.map_zero_eq_one, one_smul] at h
    exact h.symm
  rw [h2, T_smul', (hH F E σ d _ (hrho b Φ hΦ) Z X).1, (hH F E σ d Φ hΦ Z' (X + Z)).2]

end PositivityTheory.SiegelWeilFormula.KFP

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.LrhoPf =====

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.NormAddSmulSq =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.NormAddSmulSq", "h": "module\n\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinOneMulEqZeroIff\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.THeis\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinRealAdSmulAlt\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.LrhoPf\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

def ev (w : Vw d) (z : ℂ) (u : Vw d) : ℂ :=
  2 * Real.pi * Complex.I * z.re * z.im * ((‖w‖ ^ 2 : ℝ) : ℂ) -
    4 * Real.pi * Complex.I * z.im * (⟪w, u⟫_ℝ + z.re * ((‖w‖ ^ 2 : ℝ) : ℂ)) +
    ((-(2 * Real.pi * (‖u‖ ^ 2 + 2 * z.re * ⟪w, u⟫_ℝ + z.re ^ 2 * ‖w‖ ^ 2)) : ℝ) : ℂ)

def bv (w : Vw d) (z : ℂ) (u : Vw d) : ℂ := star (Complex.exp (ev w z u))

theorem norm_add_smul_sq (w u : Vw d) (x : ℝ) :
    ‖u + x • w‖ ^ 2 = ‖u‖ ^ 2 + 2 * x * ⟪w, u⟫_ℝ + x ^ 2 * ‖w‖ ^ 2 := by
  rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, real_inner_comm]
  ring

theorem T_vline (hH : THeis) (R : RD d) {g : Yf d → ℂ} {Ω : d.Fn} (hΩ : Ω ∈ d.sch) (hTΩ : d.T Ω = vac R g)
    {W : Mx F E d.m d.n} (hW : finOne F • W = 0) (z : ℂ) (X : Mx F E d.m d.n) :
    d.T (d.dd.rho d.B.ψ (vline R W z) Ω) X = bv (arc R W) z (arc R X) * g (fin d X) := by
  unfold vline
  rw [T_rho_sum' hH hΩ, _root_.PositivityTheory.SiegelWeilFormula.KFP.psi_sp' R hW, _root_.PositivityTheory.SiegelWeilFormula.KFP.psi_tw' R hW, hTΩ]
  simp only [vac]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.gau_eq', _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_add', _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_realAd', _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_add_of' R (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_realAd_smul' hW z.re)]
  simp only [bv, ev]
  rw [show star (Complex.exp _) = Complex.exp (conj _) from (Complex.exp_conj _).symm, Complex.ofReal_exp,
    ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, norm_add_smul_sq]
  simp only [map_add (f := _), map_sub, map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem continuous_bv (w : Vw d) (z : ℂ) : Continuous (bv w z) := by
  unfold bv ev
  refine continuous_star.comp (Complex.continuous_exp.comp ?_)
  fun_prop

theorem norm_bv_le (w : Vw d) (z : ℂ) (u : Vw d) : ‖bv w z u‖ ≤ 1 := by
  unfold bv
  rw [norm_star, Complex.norm_exp]
  apply Real.exp_le_one_iff.2
  have h : ‖u‖ ^ 2 + 2 * z.re * ⟪w, u⟫_ℝ + z.re ^ 2 * ‖w‖ ^ 2 ≥ 0 := by
    rw [← norm_add_smul_sq]
    positivity
  simp only [ev, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, Complex.add_im, Complex.mul_im]
  nlinarith [Real.pi_pos]

end PositivityTheory.SiegelWeilFormula.KFP

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.NormAddSmulSq =====

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.ExpAlg =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.ExpAlg", "h": "module\n\nimport Mathlib\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinOneMulEqZeroIff\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.THeis\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.FinRealAdSmulAlt\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.NormAddSmulSq\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exp_alg (s t N a U : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * s * t * N - 4 * Real.pi * Complex.I * t * (a + s * N) +
      ((-(2 * Real.pi * (U + 2 * s * a + s ^ 2 * N)) : ℝ) : ℂ)) =
      ((Real.exp (-(1 / (16 * Real.pi) * (s ^ 2 + t ^ 2) * (16 * Real.pi ^ 2 * N))) : ℝ) : ℂ) *
        (Complex.exp (-((s + t * Complex.I) ^ 2 * ((16 * Real.pi ^ 2 * N : ℝ) : ℂ) / (16 * Real.pi))) *
          ((Real.exp (-(2 * Real.pi * U)) : ℝ) : ℂ) * Complex.exp ((s + t * Complex.I) * ((-(4 * Real.pi) * a : ℝ) : ℂ))) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  linear_combination ((t : ℂ) ^ 2 * N) * Complex.I_sq

variable {d : SD σ}

theorem B_vline (hT : TAll) (hU : TUnit) (hH : THeis) (hA : AuxiliaryPrimeFunction) (hF : FockMem) (R : RD d) :
    ∃ (C : ℂ) (c s : ℝ) (ν : Measure (Mx F E d.m d.n)) (νf : Measure (Yf d)), C ≠ 0 ∧ s ≠ 0 ∧
      ν.IsAddHaarMeasure ∧ νf.IsAddHaarMeasure ∧
      ∀ g ∈ SB (Yf d), ∀ Ω ∈ d.sch, d.T Ω = vac R g → ∀ Φ ∈ d.sch, ∀ W : Mx F E d.m d.n, finOne F • W = 0 → ∀ z : ℂ,
        B ν Φ (d.dd.rho d.B.ψ (vline R W z) Ω) = C * Real.exp (-(c * ‖z‖ ^ 2 * ‖s • arc R W‖ ^ 2)) *
          (Complex.exp (-(z ^ 2 * ‖s • arc R W‖ ^ 2 / (16 * Real.pi))) *
            ∫ u, hg R νf (d.T Φ) g u * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2)) *
              Complex.exp (z * ⟪s • arc R W, u⟫_ℝ)) := by
  obtain ⟨νf, hνf, hν⟩ := exists_nuf R
  refine ⟨1, 1 / (16 * Real.pi), -(4 * Real.pi), Measure.map (jnp R) ((volume : Measure (Vw d)).prod νf), νf,
    one_ne_zero, neg_ne_zero.2 (by positivity), hν, hνf, ?_⟩
  intro g hg' Ω hΩ hTΩ Φ hΦ W hW z
  set w := arc R W with hw
  let e : Vw d → ℂ := ev w z
  let b : Vw d → ℂ := bv w z
  have hTv : ∀ X, d.T (d.dd.rho d.B.ψ (vline R W z) Ω) X = b (arc R X) * g (fin d X) :=
    T_vline hH R hΩ hTΩ hW z
  have hb : Continuous b := continuous_bv w z
  have hb1 : ∀ u, ‖b u‖ ≤ 1 := norm_bv_le w z
  have hTΦ : d.T Φ ∈ d.schM := (hT.1 F E σ d).1 Φ hΦ
  have e1 : B (Measure.map (jnp R) ((volume : Measure (Vw d)).prod νf)) Φ (d.dd.rho d.B.ψ (vline R W z) Ω) =
      ∫ u, star (b u) * hg R νf (d.T Φ) g u := by
    simp only [B, hTv]
    exact integral_jnp R hνf hTΦ hg' hb hb1
  refine e1.trans ?_
  have key : ∀ u, star (b u) * hg R νf (d.T Φ) g u =
      ((Real.exp (-(1 / (16 * Real.pi) * ‖z‖ ^ 2 * ‖(-(4 * Real.pi)) • w‖ ^ 2)) : ℝ) : ℂ) *
        Complex.exp (-(z ^ 2 * (‖(-(4 * Real.pi)) • w‖ ^ 2 : ℝ) / (16 * Real.pi))) *
          (hg R νf (d.T Φ) g u * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2)) *
            Complex.exp (z * ⟪(-(4 * Real.pi)) • w, u⟫_ℝ)) := by
    intro u
    have hz : z = z.re + z.im * Complex.I := (Complex.re_add_im z).symm
    have h1 := exp_alg z.re z.im (‖w‖ ^ 2) ⟪w, u⟫_ℝ (‖u‖ ^ 2)
    rw [← hz] at h1
    have hn : ‖(-(4 * Real.pi)) • w‖ ^ 2 = 16 * Real.pi ^ 2 * ‖w‖ ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring
    have hi : ⟪(-(4 * Real.pi)) • w, u⟫_ℝ = -(4 * Real.pi) * ⟪w, u⟫_ℝ := real_inner_smul_left _ _ _
    have hzn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
    simp only [b, bv, star_star, hn, hi, hzn]
    have h2 : ev w z u = 2 * Real.pi * Complex.I * z.re * z.im * ((‖w‖ ^ 2 : ℝ) : ℂ) -
        4 * Real.pi * Complex.I * z.im * (⟪w, u⟫_ℝ + z.re * ((‖w‖ ^ 2 : ℝ) : ℂ)) +
        ((-(2 * Real.pi * (‖u‖ ^ 2 + 2 * z.re * ⟪w, u⟫_ℝ + z.re ^ 2 * ‖w‖ ^ 2)) : ℝ) : ℂ) := by
      rfl
    rw [h2, h1]
    ring
  simp_rw [key]
  rw [integral_const_mul]
  simp only [one_mul, Complex.ofReal_exp]
  push_cast
  ring

end PositivityTheory.SiegelWeilFormula.KFP

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.ExpAlg =====
