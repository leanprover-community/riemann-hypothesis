module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiagScaleApply
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.CokerL

open PowerSeries GlobalTheory.BK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]


omit [NeZero e] in
theorem act_inertia_diagScale {P : PhiMod O K l e a ι} (Δ : Descent P) (ξ : rootsOfUnity e K)
    (s : ZMod a → K) (w : Vec K a ι) :
    Δ.act (TameGal.inertia ξ) (diagScale K a ι s w) =
      diagScale K a ι s (Δ.act (TameGal.inertia ξ) w) := by
  have h1 (u : Vec K a ι) : diagScale K a ι s u = (fun τ => (C (s τ) : K⟦X⟧)) • u := by
    ext τ i : 2
    simp [diagScale_apply, smul_eq_C_mul]
  have h2 : ringAct (TameGal.inertia ξ : TameGal K l e a) (fun τ => (C (s τ) : K⟦X⟧)) =
      fun τ => C (s τ) := by
    ext τ n
    rw [ringAct_apply, TameGal.shift_inertia, sub_zero, coeff_rescale, coeff_C]
    split_ifs with h <;> simp [h]
  rw [h1, h1, Δ.act_smul_tot, h2]

theorem isoProj_mem_isotypic {P : PhiMod O K l e a ι} (Δ : Descent P) (c : ZMod e)
    (v : Vec K a ι) : isoProj Δ c v ∈ Δ.isotypic c := by
  letI := Fintype.ofFinite (rootsOfUnity e K)
  unfold isoProj
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  intro ξ τ

  simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum, act_inertia_diagScale,
  Finset.sum_apply, diagScale_apply, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft ξ) _ _ fun ζ => ?_
  rw [Equiv.coe_mulLeft, ← Module.End.mul_apply, ← map_mul, ← map_mul, smul_smul]
  congr 1
  rw [map_mul, TameGal.root_mul, TameGal.shift_inertia, sub_zero, ← mul_pow, mul_inv,
    mul_inv_cancel_left₀ (TameGal.root_ne_zero _ _)]

theorem isoProj_mem_isotypic' : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι)
    (Δ : Descent P) (c : ZMod e) (v : Vec K a ι), GlobalTheory.CokerL.isoProj Δ c v ∈ Δ.isotypic c :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Δ c v => isoProj_mem_isotypic Δ c v

end GlobalTheory.CokerL
