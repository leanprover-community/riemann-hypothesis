import Formalism.LocalToGlobal.IndefiniteReal.ModelConjugation
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.HarishChandraMultiplicityBound
import Formalism.LocalToGlobal.IndefiniteReal.MultGood
import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank
import Formalism.LocalRingCardinality.PosOfIsomEmb
import Formalism.SharpRestriction.Divisibility.FunctionModelRallisFromInputs
import Mathlib
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLw
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Matrix

namespace Formalism.IndefR.DiscreteSeriesPlaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

structure PlaceDat (V : HSp D) (S : D.what₂.Tau → SPar) (τ : D.what₂.Tau) where
  lam : Fin V.rank → ℝ
  ε : Fin V.rank → Bool
  fr : Matrix (Fin V.rank) (Fin V.rank) ℂ
  enum : IsEnum (S τ) lam ε
  hc : Formalism.QuantumDeterminants.IsHCParam lam
  h : ℝ
  gap : Formalism.QuantumDeterminants.GapAtLeast ε lam h
  big : (ReciprocityTheory.ChartRestriction.DS.pOf ε = 0 ∨ ReciprocityTheory.ChartRestriction.DS.qOf ε = 0) ∨
    max (2 * (V.rank : ℝ)) (8 * (V.rank : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ)) < h
  fr_unit : IsUnit fr
  fr_gram : frᴴ * Formalism.REAL.Jm ε * fr = gramAt D V τ


end Formalism.IndefR.DiscreteSeriesPlaces

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult Matrix

namespace Formalism.IndefR.DiscreteSeriesPlaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem lamAt_anti {R : Ranks} (hc : HCParam R) {d c : ℕ} (hdc : d ≤ c) (hc' : c < R.r) :
    lamAt hc c ≤ lamAt hc d := by
  have := lamAt_add_add_le hc (c - d) d (by omega)
  rw [show d + (c - d) = c by omega] at this
  have h0 : (0 : ℚ) ≤ ((c - d : ℕ) : ℚ) := by positivity
  linarith


theorem isEnum_dual {n : ℕ} {S : SPar} {lam : Fin n → ℝ} {ε : Fin n → Bool} (h : IsEnum S lam ε) :
    IsEnum (dualPar S) (fun a => -lam (Fin.rev a)) (fun a => ε (Fin.rev a)) := by
  obtain ⟨hanti, Q, hQ, rfl⟩ := h
  refine ⟨fun a b hab => neg_lt_neg (hanti (Fin.rev_lt_rev.mpr hab)), fun a => -Q (Fin.rev a),
    fun a => by simp [hQ], ?_⟩
  unfold dualPar
  rw [Finset.image_image]
  ext ⟨x, s⟩
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨Fin.rev a, by simpa using ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨_, ha⟩



section Rec

variable (D : D7) (τ : D.what₂.Tau)

end Rec

section Rec2

variable (D : D7) (τ : D.what₂.Tau)

end Rec2



end Formalism.IndefR.DiscreteSeriesPlaces

end
end

section
noncomputable section

open Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult

namespace Formalism.IndefR.ModelConjugation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isEnum_unique {n : ℕ} {S : SPar} {lam lam' : Fin n → ℝ} {ε ε' : Fin n → Bool}
    (h : IsEnum S lam ε) (h' : IsEnum S lam' ε') : lam = lam' ∧ ε = ε' := by
  obtain ⟨ha, q, hq, hS⟩ := h
  obtain ⟨ha', q', hq', hS'⟩ := h'
  have key : ∀ a, ∃ b, q' b = q a ∧ ε' b = ε a := by
    intro a
    have hm : (q a, ε a) ∈ S := by rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    rw [hS'] at hm
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp hm
    exact ⟨b, congrArg Prod.fst hb, congrArg Prod.snd hb⟩
  have key' : ∀ b, ∃ a, q a = q' b := by
    intro b
    have hm : (q' b, ε' b) ∈ S := by rw [hS']; exact Finset.mem_image_of_mem _ (Finset.mem_univ b)
    rw [hS] at hm
    obtain ⟨a, -, hqa⟩ := Finset.mem_image.mp hm
    exact ⟨a, congrArg Prod.fst hqa⟩
  have hm1 : StrictMono fun a => OrderDual.toDual (lam a) := fun a b hab =>
    OrderDual.toDual_lt_toDual.2 (ha hab)
  have hm2 : StrictMono fun a => OrderDual.toDual (lam' a) := fun a b hab =>
    OrderDual.toDual_lt_toDual.2 (ha' hab)
  have hr : Set.range (fun a => OrderDual.toDual (lam a)) = Set.range (fun a => OrderDual.toDual (lam' a)) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb, -⟩ := key a
      exact ⟨b, by simp only [hq, hq', hb]⟩
    · rintro ⟨b, rfl⟩
      obtain ⟨a, hqa⟩ := key' b
      exact ⟨a, by simp only [hq, hq', hqa]⟩
  have hl : lam = lam' := by
    have := (StrictMono.range_inj hm1 hm2).mp hr
    funext a
    exact congrArg OrderDual.ofDual (congrFun this a)
  refine ⟨hl, funext fun a => ?_⟩
  obtain ⟨b, hb, he⟩ := key a
  have hab : b = a := by
    apply ha'.injective
    rw [hq' b, hb, ← hq a, hl]
  rw [← he, hab]

theorem rank_zeroth_component_eq (D : D7) : (D.sp.Y 0).rank = D.R.r := by
  rw [D.sp.Y_rank 0 (Nat.zero_le _)]; simp [Ranks.rankY]


theorem lamS_eq (R : Ranks) (P : HCParam R) (i : Fin R.r) : Formalism.MainNotions.S.lamS R P i = ((lamAt P i : ℚ) : ℝ) := by
  unfold Formalism.MainNotions.S.lamS lamAt
  split_ifs <;> simp






variable {D : D7}

def frC (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (τ : D.what₂.Tau) : Matrix (Fin (D.sp.Y 0).rank) (Fin X.B.I.n) ℂ :=
  ((D.sp.Y 0).frame.toMatrix X.bas).map (tauE D τ)

def frC' (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (τ : D.what₂.Tau) : Matrix (Fin X.B.I.n) (Fin (D.sp.Y 0).rank) ℂ :=
  (X.bas.toMatrix (D.sp.Y 0).frame).map (tauE D τ)



theorem gram_change (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (v : NumberField.InfinitePlace X.B.I.F) :
    (frC X (X.pl v))ᴴ * gramAt D (D.sp.Y 0) (X.pl v) * frC X (X.pl v) = X.B.I.J.map (X.B.I.φ v) := by
  ext i j
  rw [Matrix.map_apply, X.φ_eq, X.J_eq]
  show _ = tauE D (X.pl v) ((D.sp.Y 0).hT (X.bas i) (X.bas j))
  rw [← (D.sp.Y 0).frame.sum_repr (X.bas i), ← (D.sp.Y 0).frame.sum_repr (X.bas j)]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_mul,
    RingHom.id_apply, starRingEnd_apply, Eqv.tauE_star, Matrix.mul_apply, conjTranspose_apply, frC, gramAt,
    Matrix.map_apply, Module.Basis.toMatrix_apply, HSpace.gram]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

variable {S : D.what₂.Tau → SPar}

def Afr (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (M : DSModel (D.sp.Y 0) S) (v : NumberField.InfinitePlace X.B.I.F) :
    Matrix (Fin (D.sp.Y 0).rank) (Fin X.B.I.n) ℂ :=
  M.fr (X.pl v) * frC X (X.pl v) * X.B.I.P v

def Afr' (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (M : DSModel (D.sp.Y 0) S) (v : NumberField.InfinitePlace X.B.I.F) :
    Matrix (Fin X.B.I.n) (Fin (D.sp.Y 0).rank) ℂ :=
  (X.B.I.P v)⁻¹ * frC' X (X.pl v) * (M.fr (X.pl v))⁻¹





end Formalism.IndefR.ModelConjugation
end
end
