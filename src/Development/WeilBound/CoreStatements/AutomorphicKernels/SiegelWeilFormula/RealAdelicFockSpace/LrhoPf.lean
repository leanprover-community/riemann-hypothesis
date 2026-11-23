module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.Spf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.THeis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartz
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaParabolic.LRhoOm
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

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
