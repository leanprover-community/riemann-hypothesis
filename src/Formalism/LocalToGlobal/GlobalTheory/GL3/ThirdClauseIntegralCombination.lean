module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.LocalToGlobal.GlobalTheory.GL3.DlAppendSingle
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.KernelLattices.LateralTheory

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

section Int

variable {σ : Type*} {p : ℕ} [Fact p.Prime]

theorem isPadicIntegral_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ_[p]) (h : ∀ i ∈ s, IsIntP (f i)) :
    IsIntP (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => unfold IsIntP; simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact isPadicIntegral_add (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem isPadicIntegral_mul {x y : ℂ_[p]} (hx : IsIntP x) (hy : IsIntP y) : IsIntP (x * y) := by
  unfold IsIntP at *
  rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy

theorem integralMv_mul {F G : MvPowerSeries σ ℂ_[p]} (hF : IntegralMv F) (hG : IntegralMv G) :
    IntegralMv (F * G) := fun n => by
  classical
  rw [MvPowerSeries.coeff_mul]
  exact isPadicIntegral_sum _ _ fun x _ => isPadicIntegral_mul (hF _) (hG _)

end Int

section Subst

variable {p : ℕ} [Fact p.Prime]

theorem cc_psubst' {ι : Type*} {a : MvPowerSeries ι ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    {f : PowerSeries ℂ_[p]} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [PowerSeries.subst_mul hs, PowerSeries.subst_X hs, map_mul, ha, zero_mul]

theorem cc_flog (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries.constantCoeff (flog W wq) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, flog, PowerSeries.coeff_mk, if_pos rfl]

variable {D : D7} {N N' r : ℕ} (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
  (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p]) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)

def atLogA : D.what₂.Tau × Fin N' × Fin N → MvPowerSeries (Fin r) ℂ_[p] :=
  fun k => ∑ i, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p])
      (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * lamC lam (embT D k.1 (b i k.2.1 k.2.2))) *
      PowerSeries.subst (MvPowerSeries.X i) (flog (C • wModel lam Λ) wq)

theorem atLogA_hasSubst : MvPowerSeries.HasSubst (atLogA lam Λ C wq b) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro k

  simp only [atLogA, map_sum, map_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [cc_psubst' (MvPowerSeries.constantCoeff_X i) (cc_flog _ wq), mul_zero]

theorem atLog_eq (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    atLog D lam Λ C wq b F = MvPowerSeries.substAlgHom (atLogA_hasSubst lam Λ C wq b) F := by
  rw [MvPowerSeries.coe_substAlgHom]; rfl

end Subst

section Clauses

variable {D : D7} (T : Tor D) {N N' : ℕ} {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
  (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))

end Clauses

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC
