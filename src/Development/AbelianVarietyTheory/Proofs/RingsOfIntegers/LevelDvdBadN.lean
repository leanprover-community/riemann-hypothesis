import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TrivLevel

theorem level_dvd_badN (D : D7) {p : ℕ} (hp : p ∈ D.host.levelPrimes) : p ∣ badN D :=
  dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hp) _


theorem badN_pos_iff (D : D7) : 0 < badN D ↔ 0 ∉ D.host.levelPrimes := by
  have h := D.host.qd_big
  constructor
  · intro hb h0
    exact hb.ne' (Nat.eq_zero_of_zero_dvd (level_dvd_badN D h0))
  · intro h0
    unfold badN
    refine Nat.mul_pos (Nat.mul_pos (Nat.mul_pos D.host.QS_pos (by omega)) (by omega)) (Finset.prod_pos fun p hp => ?_)
    exact Nat.pos_of_ne_zero fun e => h0 (e ▸ hp)

theorem coprime_level {D : D7} (T : Full D) (hF : LawsFull T) (j : ℕ) (hj : InR D j) (n : ℕ) {k : ℕ}
    (hk : Nat.Coprime k (badN D)) : Nat.Coprime k (T.dδ j n).l₂.M := by
  have hM : (T.dδ j n).l₂.M = T.Q.l.M * (T.dδ j n).pd := (hF.sh.dLev j hj n).2.1
  have hl : T.Q.l.M = D.host.g 0 * D.host.g 1 := hF.p.toLawsCore.pins.2.1.1
  have hc : ∀ p ∈ D.host.levelPrimes, Nat.Coprime k p := fun p hp =>
    Nat.Coprime.coprime_dvd_right (level_dvd_badN D hp) hk
  obtain ⟨p, hp, hpd⟩ := hF.sh.dPd
  have hpl : p ∈ D.host.levelPrimes := by
    rcases hp with rfl | rfl
    exacts [D.host.pde_level.1, D.host.pde_level.2]
  rw [hM, hl, hpd j hj n]
  exact ((hc _ (D.host.g_level 0)).mul_right (hc _ (D.host.g_level 1))).mul_right (hc p hpl)


end GlobalTheory.TrivLevel
