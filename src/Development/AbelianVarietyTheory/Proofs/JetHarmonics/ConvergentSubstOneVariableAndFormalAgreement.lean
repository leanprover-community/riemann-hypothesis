module

public import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.ConvSer.Bridge

def unitExp : ℕ ≃ (Unit →₀ ℕ) where
  toFun n := Finsupp.single () n
  invFun ν := ν ()
  left_inv n := by simp
  right_inv ν := by ext; simp

variable {K : Type} [NormedField K]

theorem powerSeriesConvergentSubstMv_eq_mv {τ : Type} (s : MvPowerSeries τ K) (f : PowerSeries K) :
    csub1 s f = csub (fun _ : Unit => s) f := by
  ext μ
  change ∑' n : ℕ, PowerSeries.coeff n f * MvPowerSeries.coeff μ (s ^ n) =
    ∑' ν : Unit →₀ ℕ, MvPowerSeries.coeff ν f * MvPowerSeries.coeff μ (∏ i : Unit, s ^ ν i)
  rw [← unitExp.tsum_eq]
  refine tsum_congr fun n => ?_
  simp [unitExp]

theorem powerSeriesEvalTsum_eq_mvPowerSeriesEvalTsum (f : PowerSeries K) (t : K) : ev1 f t = ev f (fun _ : Unit => t) := by
  unfold ev1 ev
  rw [← unitExp.tsum_eq]
  refine tsum_congr fun n => ?_
  simp [unitExp]

theorem powerSeriesHasSumAt_iff_mvPowerSeriesHasSumAt (f : PowerSeries K) (t a : K) : PowerSeriesHasSumAt f t a ↔ HS f (fun _ : Unit => t) a := by
  unfold PowerSeriesHasSumAt HS
  rw [← unitExp.hasSum_iff]
  have h : (fun ν : Unit →₀ ℕ => MvPowerSeries.coeff ν f * ∏ i : Unit, t ^ ν i) ∘ unitExp =
      fun n : ℕ => PowerSeries.coeff n f * t ^ n := by
    funext n
    simp [unitExp]
  rw [h]

theorem csub_C {σ τ : Type} [Fintype σ] (S : MvPowerSeries σ K) (x : σ → K) :
    csub (fun i => (MvPowerSeries.C (x i) : MvPowerSeries τ K)) S = MvPowerSeries.C (ev S x) := by
  have hC : ∀ ν : σ →₀ ℕ, (∏ i, (MvPowerSeries.C (x i) : MvPowerSeries τ K) ^ ν i) =
      MvPowerSeries.C (∏ i, x i ^ ν i) := fun ν => by simp [map_prod, map_pow]
  ext μ
  change ∑' ν : σ →₀ ℕ, MvPowerSeries.coeff ν S *
      MvPowerSeries.coeff μ (∏ i, (MvPowerSeries.C (x i) : MvPowerSeries τ K) ^ ν i) = _
  simp only [hC]
  by_cases h : μ = 0
  · subst h
    simp only [MvPowerSeries.coeff_zero_C]
    rfl
  · simp only [MvPowerSeries.coeff_C_of_ne_zero h, mul_zero, tsum_zero]

theorem shift1_eq_csub (F : MvPowerSeries (Fin 2) K) (y : K) :
    shift1 F y = csub (![PowerSeries.X, PowerSeries.C y] : Fin 2 → MvPowerSeries Unit K) F := by
  ext m
  have hc : ∀ p : PowerSeries K, MvPowerSeries.coeff (unitExp m) p = PowerSeries.coeff m p :=
    fun p => by simp [unitExp]
  change PowerSeries.coeff m (shift1 F y) = ∑' ν : Fin 2 →₀ ℕ, MvPowerSeries.coeff ν F *
    MvPowerSeries.coeff (unitExp m)
      (∏ i, (![PowerSeries.X, PowerSeries.C y] : Fin 2 → MvPowerSeries Unit K) i ^ ν i)
  have hterm : ∀ ν : Fin 2 →₀ ℕ, MvPowerSeries.coeff ν F * MvPowerSeries.coeff (unitExp m)
      (∏ i, (![PowerSeries.X, PowerSeries.C y] : Fin 2 → MvPowerSeries Unit K) i ^ ν i) =
      MvPowerSeries.coeff ν F * (if m = ν 0 then y ^ ν 1 else 0) := by
    intro ν
    rw [hc, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← map_pow, mul_comm (PowerSeries.X ^ _), PowerSeries.coeff_C_mul_X_pow]
  simp only [hterm]
  rw [shift1, PowerSeries.coeff_mk]
  have hinj : Function.Injective
      (fun b : ℕ => Finsupp.single (0 : Fin 2) m + Finsupp.single 1 b) := by
    intro b b' h
    have h1 := congrArg (fun ν : Fin 2 →₀ ℕ => ν 1) h
    simpa using h1
  have hsupp : Function.support
      (fun ν : Fin 2 →₀ ℕ => MvPowerSeries.coeff ν F * (if m = ν 0 then y ^ ν 1 else 0)) ⊆
      Set.range (fun b : ℕ => Finsupp.single (0 : Fin 2) m + Finsupp.single 1 b) := by
    intro ν hν
    have h0 : m = ν 0 := by
      by_contra h
      exact hν (by simp [h])
    refine ⟨ν 1, ?_⟩
    ext i
    fin_cases i <;> simp [h0]
  refine Eq.trans ?_ (hinj.tsum_eq hsupp)
  refine tsum_congr fun b => ?_
  simp

theorem csub_eq_subst {σ τ : Type} [Fintype σ] (a : σ → MvPowerSeries τ K)
    (S : MvPowerSeries σ K) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) :
    csub a S = MvPowerSeries.subst a S := by
  have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  ext μ
  rw [MvPowerSeries.coeff_subst hs, ← tsum_eq_finsum (L := SummationFilter.unconditional (σ →₀ ℕ))
    (MvPowerSeries.coeff_subst_finite hs S μ)]
  change ∑' ν : σ →₀ ℕ, MvPowerSeries.coeff ν S * MvPowerSeries.coeff μ (∏ i, a i ^ ν i) = _
  refine tsum_congr fun ν => ?_
  rw [smul_eq_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]

theorem powerSeriesConvergentSubstMv_eq_subst {τ : Type} (a : MvPowerSeries τ K) (f : PowerSeries K)
    (ha : MvPowerSeries.constantCoeff a = 0) : csub1 a f = f.subst a := by
  rw [powerSeriesConvergentSubstMv_eq_mv, csub_eq_subst _ _ (fun _ => ha)]
  rfl

theorem csub_bridge : ∀ (K : Type) [NormedField K], (∀ (τ : Type) (s : MvPowerSeries τ K) (f : PowerSeries K), csub1 s f = csub (fun _ : Unit => s) f) ∧ (∀ (f : PowerSeries K) (t : K), ev1 f t = ev f (fun _ : Unit => t)) ∧ (∀ (f : PowerSeries K) (t a : K), PowerSeriesHasSumAt f t a ↔ HS f (fun _ : Unit => t) a) ∧ (∀ (σ τ : Type) [Fintype σ] (S : MvPowerSeries σ K) (x : σ → K), csub (fun i => (MvPowerSeries.C (x i) : MvPowerSeries τ K)) S = MvPowerSeries.C (ev S x)) ∧ (∀ (F : MvPowerSeries (Fin 2) K) (y : K), shift1 F y = csub (![PowerSeries.X, PowerSeries.C y] : Fin 2 → MvPowerSeries Unit K) F) ∧ (∀ (σ τ : Type) [Fintype σ] (a : σ → MvPowerSeries τ K) (S : MvPowerSeries σ K), (∀ i, MvPowerSeries.constantCoeff (a i) = 0) → csub a S = MvPowerSeries.subst a S) ∧ (∀ (τ : Type) (a : MvPowerSeries τ K) (f : PowerSeries K), MvPowerSeries.constantCoeff a = 0 → csub1 a f = f.subst a) := by
  intro K _
  exact ⟨fun _ s f => powerSeriesConvergentSubstMv_eq_mv s f, fun f t => powerSeriesEvalTsum_eq_mvPowerSeriesEvalTsum f t, fun f t a => powerSeriesHasSumAt_iff_mvPowerSeriesHasSumAt f t a,
    fun _ _ _ S x => csub_C S x, fun F y => shift1_eq_csub F y,
    fun _ _ _ a S ha => csub_eq_subst a S ha, fun _ a f ha => powerSeriesConvergentSubstMv_eq_subst a f ha⟩

end GlobalTheory.ConvSer.Bridge
