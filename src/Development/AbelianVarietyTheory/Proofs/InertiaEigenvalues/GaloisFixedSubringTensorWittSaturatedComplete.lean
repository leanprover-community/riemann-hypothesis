module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodOfComplete
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
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl.FixL

theorem fix_of_mul {R : Type} [CommRing R] (p : ℕ) (h : ∀ x : R, (p : R) * x = 0 → x = 0)
    (f : R →+* R) (x : R) (hx : f ((p : R) * x) = (p : R) * x) : f x = x := by
  have hf : f (p : R) = (p : R) := map_natCast f p
  have h2 : (p : R) * (f x - x) = 0 := by
    rw [mul_sub, ← hf, ← map_mul, hx, hf, sub_self]
  exact sub_eq_zero.mp (h _ h2)

theorem fix_of_sum {R : Type} [CommRing R] (p : ℕ)
    (h : ∀ x : R, (∀ k : ℕ, ∃ r, x = (p : R) ^ k * r) → x = 0)
    (f : R →+* R) (x : ℕ → R) (hx : ∀ i, f (x i) = x i) (y : R)
    (hy : ∀ k : ℕ, ∃ r, y - ∑ i ∈ Finset.range k, (p : R) ^ i * x i = (p : R) ^ k * r) :
    f y = y := by
  apply sub_eq_zero.mp
  apply h
  intro k
  obtain ⟨r, hr⟩ := hy k
  have hsum : f (∑ i ∈ Finset.range k, (p : R) ^ i * x i) = ∑ i ∈ Finset.range k, (p : R) ^ i * x i := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_mul, map_pow, map_natCast, hx]
  have hfy : f y - ∑ i ∈ Finset.range k, (p : R) ^ i * x i = (p : R) ^ k * f r := by
    rw [← hsum, ← map_sub, hr, map_mul, map_pow, map_natCast]
  refine ⟨f r - r, ?_⟩
  rw [mul_sub, ← hfy, ← hr]
  ring

theorem frob_comm {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l)
    (g : GQ l) (x : RW LL) : AI.gRW LL g (φRW LL x) = φRW LL (AI.gRW LL g x) := by
  have key : ∀ w : WCb l, AI.actWCbHom g (frobW l w) = frobW l (AI.actWCbHom g w) := by
    intro w
    unfold LocAinf.actWCbHom frobW
    simp only [MonoidHom.coe_mk, OneHom.coe_mk]
    unfold mapAlgEquivW
    ext n
    dsimp only [AlgEquiv.ofRingEquiv]
    simp [mapEquivW, WittVector.map_coeff, frobenius_def]
  have hc : ((AI.actWCbHom g : WCb l →ₐ[ℤ_[l]] WCb l).comp (frobW l)) =
      (frobW l).comp (AI.actWCbHom g : WCb l →ₐ[ℤ_[l]] WCb l) := AlgHom.ext key
  unfold LocAinf.gRW φRW
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp,
    ← Algebra.TensorProduct.map_comp, hc]

theorem fixSub_ladic (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l)
    (H : Set (GQ l)) :
    (∀ x, (l : RW LL) * x ∈ fixSub AI LL H → x ∈ fixSub AI LL H) ∧
    (∀ x ∈ fixSub AI LL H, φRW LL x ∈ fixSub AI LL H) ∧
    ∀ x : ℕ → RW LL, (∀ i, x i ∈ fixSub AI LL H) → ∃ y ∈ fixSub AI LL H, ∀ k : ℕ, ∃ r,
      y - ∑ i ∈ Finset.range k, (l : RW LL) ^ i * x i = (l : RW LL) ^ k * r := by
  obtain ⟨h0, h1, h2⟩ := GlobalTheory.Decompl.LAdic.ladic_RW l LL
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [mem_fixSub] at hx ⊢
    intro g hg
    exact fix_of_mul l h0 (AI.gRW LL g : RW LL →+* RW LL) x (hx g hg)
  · intro x hx
    rw [mem_fixSub] at hx ⊢
    intro g hg
    rw [frob_comm, hx g hg]
  · intro x hx
    obtain ⟨s, hs⟩ := h2 x
    refine ⟨s, ?_, hs⟩
    rw [mem_fixSub]
    intro g hg
    exact fix_of_sum l h1 (AI.gRW LL g : RW LL →+* RW LL) x
      (fun i => mem_fixSub.1 (hx i) g hg) s hs

end GlobalTheory.Decompl.FixL
