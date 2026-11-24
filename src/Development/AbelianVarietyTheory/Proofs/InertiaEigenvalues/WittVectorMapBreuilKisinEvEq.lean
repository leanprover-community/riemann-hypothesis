module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorTeichmullerIsAdicCompleteOfPerfectStatement
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

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem wmap_ev_eq : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsDomain O]
    [CharP O l] [PerfectRing O l] (ψ ψ' : OCb l →+* O), ψ bk.flat ≠ 0 →
    IsAdicComplete (Ideal.span {ψ bk.flat}) O →
    (∀ s : bk.S, ψ ((bk.ev s).coeff 0) = ψ' ((bk.ev s).coeff 0)) →
    ∀ s : bk.S, WittVector.map ψ (bk.ev s) = WittVector.map ψ' (bk.ev s) := by
  intro l _ K bk O _ _ _ _ ψ ψ' h0 hc h s
  have hval : ∀ y : Fq l bk.a, ψ (Fq.val l bk.a y) = ψ' (Fq.val l bk.a y) := fun y => by
    have := h (C (WittVector.teichmuller l y))
    rwa [bk.ev_C, wA_teich, WittVector.teichmuller_coeff_zero] at this
  have hflat : ψ bk.flat = ψ' bk.flat := by
    have := h X
    rwa [bk.ev_X, WittVector.teichmuller_coeff_zero] at this
  have hX : ((WittVector.map ψ).comp bk.ev) X = WittVector.teichmuller l (ψ bk.flat) := by
    rw [RingHom.comp_apply, bk.ev_X, WittVector.map_teichmuller]
  have hcomp := (GlobalTheory.T.wittVector_teichmuller_isAdicComplete_of_perfect l O (ψ bk.flat) h0 hc).1
  refine RingHom.congr_fun (ringHom_ext_of_sep ((WittVector.map ψ).comp bk.ev) ((WittVector.map ψ').comp bk.ev)
    (fun w => ?_) ?_ fun x hx => ?_) s
  · simp only [RingHom.comp_apply, bk.ev_C]
    refine WittVector.ext fun n => ?_
    simp only [wA, AlgHom.coe_mk, WittVector.map_coeff]
    exact hval _
  · rw [hX, RingHom.comp_apply, bk.ev_X, WittVector.map_teichmuller, hflat]
  · rw [hX] at hx
    refine IsHausdorff.haus' (I := Ideal.span {WittVector.teichmuller l (ψ bk.flat)}) x fun n => ?_
    simp only [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton.2 (hx n)

end GlobalTheory.BSP
