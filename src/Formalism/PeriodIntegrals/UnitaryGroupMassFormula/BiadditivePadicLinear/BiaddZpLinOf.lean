import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BiadditivePadicLinear.Cont2
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.CoeffPowMulPowEqZeroOfLt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.PowerSeriesDiagonalLinear
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.SubstOpsHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.CoeffOneLNeZero

noncomputable section

open Classical

namespace PI.BiaddZpLinW

open PI.BiaddZpLin

theorem t0 : ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f g h f' g' : MvPowerSeries σ ℂ_[p]),
    Simeq f f ∧ (Simeq f g → Simeq g f) ∧ (Simeq f g → Simeq g h → Simeq f h) ∧
    (Simeq f g → Simeq f' g' → Simeq (f + f') (g + g')) :=
  PI.BeDiagZp.simeq_equivalence_additive

theorem t1 : ∀ (p : ℕ) [Fact p.Prime] (σ τ : Type) [Finite σ] (f g : MvPowerSeries σ ℂ_[p])
    (s : σ → MvPowerSeries τ ℂ_[p]),
    (∀ i, MvPowerSeries.constantCoeff (s i) = 0) → (∀ i, IntegralMv (s i)) →
    Simeq f g → Simeq (MvPowerSeries.subst s f) (MvPowerSeries.subst s g) :=
  PI.BeDiagZp.power_series_diagonal_linear

theorem t2 : ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.constantCoeff l = 0 →
    ∀ (σ τ : Type) [Finite σ] (s : σ → MvPowerSeries τ ℂ_[p]),
    (∀ i, MvPowerSeries.constantCoeff (s i) = 0) →
    (∀ i, MvPowerSeries.subst s (Xv i : MvPowerSeries σ ℂ_[p]) = s i) ∧
    (∀ (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]),
      MvPowerSeries.subst s (MvPowerSeries.C c * a) = MvPowerSeries.C c * MvPowerSeries.subst s a) ∧
    (∀ a b : MvPowerSeries σ ℂ_[p],
      MvPowerSeries.subst s (a + b) = MvPowerSeries.subst s a + MvPowerSeries.subst s b) ∧
    ∀ a b : MvPowerSeries σ ℂ_[p], MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.constantCoeff b = 0 →
      MvPowerSeries.constantCoeff (MvPowerSeries.subst s a) = 0 ∧
      MvPowerSeries.subst s (add l ex a b) = add l ex (MvPowerSeries.subst s a) (MvPowerSeries.subst s b) ∧
      (∀ c, MvPowerSeries.subst s (mulBy l ex c a) = mulBy l ex c (MvPowerSeries.subst s a)) ∧
      MvPowerSeries.subst s (phAt ph a) = phAt ph (MvPowerSeries.subst s a) ∧
      MvPowerSeries.subst s (be l ex ph a b) = be l ex ph (MvPowerSeries.subst s a) (MvPowerSeries.subst s b) :=
  PI.BeDiagZp.OpsW.substOps_holds

theorem t3 : ∀ (p : ℕ) [Fact p.Prime] (l ex : PowerSeries ℂ_[p]),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    PowerSeries.constantCoeff l = 0 ∧
    ∀ (σ : Type) (a b : MvPowerSeries σ ℂ_[p]),
      MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.constantCoeff b = 0 →
      MvPowerSeries.constantCoeff (add l ex a b) = 0 ∧
      (∀ c, MvPowerSeries.constantCoeff (mulBy l ex c a) = 0) ∧
      add l ex a b = add l ex b a ∧
      add l ex a a = mulBy l ex 2 a ∧
      (∀ c d, add l ex (mulBy l ex c a) (mulBy l ex d a) = mulBy l ex (c + d) a) ∧
      (∀ c, add l ex (mulBy l ex c a) a = mulBy l ex (c + 1) a) ∧
      mulBy l ex 1 a = a ∧
      mulBy l ex 0 a = 0 :=
  PI.BeDiagZp.IdentW.ident_holds

theorem t5 : ∀ (p : ℕ) [Fact p.Prime] (σ τ : Type) [Finite σ] (f : MvPowerSeries σ ℂ_[p])
    (s : σ → MvPowerSeries τ ℂ_[p]),
    (∀ i, MvPowerSeries.constantCoeff (s i) = 0) → (∀ i, IntegralMv (s i)) →
    IntegralMv f → IntegralMv (MvPowerSeries.subst s f) :=
  PI.BeDiagZp.intSubst_holds

variable {p : ℕ} [Fact p.Prime]

theorem simeq_congr {σ : Type} {f g f' g' : MvPowerSeries σ ℂ_[p]} (e : f - g = f' - g')
    (h : Simeq f g) : Simeq f' g' := by
  unfold Simeq at *
  rw [← e]
  exact h

theorem intX {σ : Type} (i : σ) : IntegralMv (Xv i : MvPowerSeries σ ℂ_[p]) := by
  intro n
  simp only [IsIntP, Xv, MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem int0 {σ : Type} : IntegralMv (0 : MvPowerSeries σ ℂ_[p]) := by
  intro n
  simp [IsIntP]

theorem ccX {σ : Type} (i : σ) : MvPowerSeries.constantCoeff (Xv i : MvPowerSeries σ ℂ_[p]) = 0 := by
  simp [Xv]



end PI.BiaddZpLinW
