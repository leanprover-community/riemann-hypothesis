import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackDescentAlongGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSubFiniteFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeQuotientByFiniteTranslations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentEndomorphismQuotientGroupScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescentLinearisedLineBundleGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGaloisCoverGrpSchemeSquareProductMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearisationBirigidifiedPowerIsotropicSec
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommutatorPairingValueHeckePoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsDiagRoot
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELTripleOfDenseFibres
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilCommutatorPairingTorsionGeometricPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingBirigidifiedTrivialOnAxesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingSwapEqOfSwapInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingDiagonalPullbackEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingPullbackPowerMapLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchemeRootOfUnityEqOneOfGeometricPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirigidifiedBundleOfDescentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBirigidifiedBundleSymmetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiInvolutionOfGaloisIsogenyDescent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalDescendedBundleGaloisCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBundleKernelKilledByIntegerPrimeToPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionsOfEtaleGaloisQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateSimilitudeHeckeTranslateGeometric

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_commutatorPairing_value_heckePoints : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h₁ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ h₂ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∃ u : Γ((𝟙_ (Over S)).left, ⊤)ˣ, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 h₂) u := by
  first | (exact @GlobalTheory.HeckeWeilLift.exists_weilIs_hecke) | (exact GlobalTheory.HeckeWeilLift.exists_weilIs_hecke) | (intros; apply GlobalTheory.HeckeWeilLift.exists_weilIs_hecke <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT.Hecke

theorem eta_nsmul {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {M : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b M s) (y : D.La) (m : ℕ) : o.eta (m • y) = o.eta y ^ m := by
  induction m with
  | zero => rw [zero_smul, pow_zero, eta_zero]
  | succ m ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]

theorem weilIs_heckeSub_pow_eq_one : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h₁ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ h₂ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ u : Γ((𝟙_ (Over S)).left, ⊤)ˣ, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 h₂) u → u ^ k = 1 := by
  intro p _ D R _ b g c k N _ _ _ _ _ _ _ S s o h₁ hh₁ h₂ _ u hu
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hA : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have hL : (lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o.isLB _ _
  obtain ⟨x, rfl⟩ := hh₁
  have hk1 : o.eta (N • g x) ^ k = 1 := by
    rw [← eta_nsmul, smul_smul, Nat.mul_comm k N]; exact o.eta_ker _
  have hxk : (lift (o.eta (N • g x)) 1 : 𝟙_ (Over S) ⟶ G2 o.A) ^ k = 1 := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [MonObj.pow_comp]; simp [hk1]
    · rw [MonObj.pow_comp]; simp
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [hk, pow_zero]
  have pw : ∀ m : ℕ, Out.WeilIs (G2 o.A) (lbPow o.P (k ^ 2 / c)) 1
      ((lift (o.eta (N • g x)) 1 : 𝟙_ (Over S) ⟶ G2 o.A) ^ (m + 1)) (lift 1 h₂) (u ^ (m + 1)) := by
    intro m
    induction m with
    | zero => simpa using hu
    | succ m ih =>
      rw [pow_succ _ (m + 1), pow_succ u (m + 1)]
      exact GlobalTheory.DiagPairing.weilIs_mul_left hG hA hL ih hu
  have hp := pw (k - 1)
  rw [Nat.sub_add_cancel hk, hxk] at hp
  have h11 := GlobalTheory.DiagPairing.weilIs_mul_left hG hA hL hp hp
  rw [_root_.mul_one] at h11
  exact mul_eq_left.1 (GlobalTheory.CommutatorPairing.weilIs_unique hG hA hL h11 hp)

end GlobalTheory.UPel.HT.Hecke
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutatorPairing_heckePoints_pow_eq_one : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h₁ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ h₂ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ u : Γ((𝟙_ (Over S)).left, ⊤)ˣ, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 h₂) u → u ^ k = 1 := by
  atlas_forward_decl GlobalTheory.UPel.HT.Hecke.weilIs_heckeSub_pow_eq_one
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT.Hecke

section GeomAux

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem liftSq_mul {T : Over S} (a b a' b' : T ⟶ A) :
    (lift a b : T ⟶ G2 A) * lift a' b' = lift (a * a') (b * b') := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [MonObj.mul_comp]; simp
  · rw [MonObj.mul_comp]; simp

theorem liftSq_pow {T : Over S} (a b : T ⟶ A) (n : ℕ) :
    (lift a b : T ⟶ G2 A) ^ n = lift (a ^ n) (b ^ n) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [MonObj.pow_comp]; simp
  · rw [MonObj.pow_comp]; simp

end GeomAux

theorem weilIs_heckeSub_geom : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h₁ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ h₂ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (β : R →+* K), x ≫ s = spMap β → ∀ u : Γ((Over.mk x).left, ⊤)ˣ, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (toUnit (Over.mk x) ≫ (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A)) (toUnit (Over.mk x) ≫ (lift 1 h₂ : 𝟙_ (Over S) ⟶ G2 o.A)) u → u = 1 := by
  intro p _ D R _ b g c k N hc hk hN hNp hEF hg hck S s o h₁ hh₁ h₂ hh₂ K _ _ x β hx u hu
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hA2 : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have hPL : o.P.IsLB := o.isLB
  obtain ⟨I, hI⟩ := o.geom K x β hx
  obtain ⟨x₁, rfl⟩ := hh₁
  obtain ⟨x₂, rfl⟩ := hh₂
  have hpp : p.Prime := Fact.out
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; exact absurd (Nat.coprime_zero_left p |>.1 hk) hpp.one_lt.ne'
    · exact h
  have hN0 : 0 < N := by omega
  obtain ⟨m, hm⟩ : ∃ m, m = k ^ 2 / c := ⟨_, rfl⟩
  rw [← hm] at hu
  have hmc : m * c = k ^ 2 := by rw [hm]; exact Nat.div_mul_cancel hck
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, zero_mul] at hmc; exact absurd hmc.symm (pow_ne_zero 2 hk0.ne')
    · exact h
  obtain ⟨j, hj0, hjp, hjpar⟩ : ∃ j : ℕ, 0 < j ∧ (j * k ^ 2).Coprime p ∧ (Even j ∨ Odd (j * k ^ 2)) := by
    by_cases h2 : p = 2
    · subst h2
      have hko : Odd k := Nat.coprime_two_right.1 hk
      exact ⟨1, one_pos, by rw [_root_.one_mul]; exact Nat.Coprime.pow_left 2 hk,
        Or.inr (by rw [_root_.one_mul]; exact hko.pow)⟩
    · refine ⟨2, two_pos, Nat.coprime_mul_iff_left.2 ⟨?_, Nat.Coprime.pow_left 2 hk⟩, Or.inl even_two⟩
      exact (Nat.coprime_primes Nat.prime_two hpp).2 (Ne.symm h2)
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = j * k ^ 2 := ⟨_, rfl⟩
  rw [← hn₀] at hjp hjpar
  have hn0 : 0 < n₀ := by rw [hn₀]; positivity

  have ev0 : ∀ n, I.ev n 0 = 1 := fun n => by
    have h := I.add n 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have evs : ∀ n (z : D.La) (r : ℕ), I.ev n (r • z) = I.ev n z ^ r := fun n z r => by
    induction r with
    | zero => rw [zero_smul, pow_zero, ev0]
    | succ r ih => rw [succ_nsmul, I.add, ih, pow_succ]
  have hdown : ∀ z : D.La, toUnit (Over.mk x) ≫ o.eta (N • g z) = I.ev n₀ (g z) ^ (j * k) := fun z => by
    have t1 := I.tower k N hk0 hN0 (Nat.coprime_mul_iff_left.2 ⟨hk, hNp⟩) (g z)
    have e : k * (j * k) = n₀ := by rw [hn₀]; ring
    have t2 := I.tower k (j * k) hk0 (by positivity) (by rw [e]; exact hjp) (g z)
    rw [Nat.mul_comm k N] at t1
    rw [hI, evs, t1, ← t2, e]
  obtain ⟨w, hw⟩ : ∃ w, w = I.ev n₀ (g x₁) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = I.ev n₀ (g x₂) := ⟨_, rfl⟩
  have ha : toUnit (Over.mk x) ≫ (lift (o.eta (N • g x₁)) 1 : 𝟙_ (Over S) ⟶ G2 o.A) =
      lift (w ^ (j * k)) (1 ^ (j * k)) := by
    rw [comp_lift, hdown, ← hw, one_pow, MonObj.comp_one]
  have hb : toUnit (Over.mk x) ≫ (lift 1 (o.eta (N • g x₂)) : 𝟙_ (Over S) ⟶ G2 o.A) =
      lift (1 ^ (j * k)) (y ^ (j * k)) := by
    rw [comp_lift, hdown, ← hy, one_pow, MonObj.comp_one]
  rw [ha, hb] at hu
  have e1 := GlobalTheory.T.commutatorPairing_pullback_powerMap_level S o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) o.P o.ab (pull_isLB hPL _) o.ample hPL
    o.rig₁ o.rig₂ m (j * k) (j * k) 1 (Over.mk x) w 1 1 y u hu

  have hwn : w ^ n₀ = 1 := (I.onto n₀ hn0 hjp w).2 ⟨g x₁, hw.symm⟩
  have hyn : y ^ n₀ = 1 := (I.onto n₀ hn0 hjp y).2 ⟨g x₂, hy.symm⟩
  have hK : ((n₀ : ℕ) : K) ≠ 0 := by
    have := (b.unit n₀ hjp).map β
    rw [map_natCast] at this
    exact this.ne_zero
  have tor : ∀ a a' : Over.mk x ⟶ o.A, a ^ n₀ = 1 → a' ^ n₀ = 1 →
      (lift a a' : Over.mk x ⟶ G2 o.A) ^ n₀ = 1 := fun a a' h h' => by
    rw [liftSq_pow, h, h']
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have one_n : (1 : Over.mk x ⟶ o.A) ^ n₀ = 1 := one_pow _
  have ex : ∀ X Y : Over.mk x ⟶ G2 o.A, X ^ n₀ = 1 → Y ^ n₀ = 1 →
      ∃ e : Γ((Over.mk x).left, ⊤)ˣ, Out.WeilIs (G2 o.A) o.P (n₀ : ℤ) X Y e := fun X Y hX hY =>
    GlobalTheory.WeilGeomPt.exists_weilIs_geomPt S (G2 o.A) o.P hA2 hPL K x n₀ hn0 hK X Y hX hY
  obtain ⟨F, hF⟩ := ex _ _ (tor w 1 hwn one_n) (tor 1 y one_n hyn)
  have hFp : ∀ r : ℕ, Out.WeilIs (G2 o.A) o.P (n₀ : ℤ) (lift (w ^ (r + 1)) 1) (lift 1 y) (F ^ (r + 1)) := by
    intro r
    induction r with
    | zero => simpa using hF
    | succ r ih =>
      have := GlobalTheory.SiegelTypings.weilIs_mul hA2 hPL ih hF
      rwa [liftSq_mul, _root_.mul_one, ← pow_succ, ← pow_succ] at this
  have hjm : j * m = (j * m - 1) + 1 := (Nat.sub_add_cancel (Nat.mul_pos hj0 hm0)).symm
  have hFjm : Out.WeilIs (G2 o.A) o.P (n₀ : ℤ) (lift (w ^ (j * m)) 1) (lift 1 y) (F ^ (j * m)) := by
    rw [hjm]; exact hFp _
  have hl1 : (GlobalTheory.UPel.HT.Hecke.lbPow o.P 1).IsLB := LB.isLB_linComb hPL _ _
  have iso1 : LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P 1) (o.P.pull (Over.Hom.left (𝟙 (G2 o.A)))) := by
    have c1 := GlobalTheory.CechPic.cls_linComb hPL (fun _ : Fin 1 => 𝟙 (G2 o.A).left) (fun _ => (1 : ℤ)) hl1
    have c2 := GlobalTheory.CechPic.cls_pull hPL (Over.Hom.left (𝟙 (G2 o.A))) (pull_isLB hPL _)
    refine (GlobalTheory.CechPic.cls_eq_iff hl1 (pull_isLB hPL _)).1 (c1.trans (Eq.trans ?_ c2.symm))
    simp
  have e2' : Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P 1) (n₀ : ℤ) (lift (w ^ (j * m)) (1 ^ 1))
      (lift (1 ^ (j * m)) (y ^ 1)) (F ^ (j * m)) := by
    rw [one_pow, one_pow, pow_one]
    exact GlobalTheory.PELFamily.weilIs_of_lbIso hG hA2 hl1 hPL iso1 hFjm
  have e2 := GlobalTheory.T.commutatorPairing_pullback_powerMap_level S o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) o.P o.ab (pull_isLB hPL _) o.ample hPL
    o.rig₁ o.rig₂ 1 (j * m) 1 (n₀ : ℤ) (Over.mk x) w 1 1 y _ e2'
  have hlev : (1 : ℤ) * ((m * (j * k) * (j * k) : ℕ) : ℤ) = (n₀ : ℤ) * ((1 * (j * m) * 1 : ℕ) : ℤ) := by
    rw [hn₀]; push_cast; ring

  have hu' : u = F ^ (j * m) := GlobalTheory.CommutatorPairing.weilIs_unique hG hA2 hPL e1 (hlev ▸ e2)

  have hgeo := I.isom n₀ hn0 hjp (g x₁) (g x₂)
  rw [← hw, ← hy] at hgeo
  obtain ⟨c11, h11⟩ := ex (lift w 1) (lift y 1) (tor w 1 hwn one_n) (tor y 1 hyn one_n)
  obtain ⟨c21, h21⟩ := ex (lift 1 w) (lift y 1) (tor 1 w one_n hwn) (tor y 1 hyn one_n)
  obtain ⟨c22, h22⟩ := ex (lift 1 w) (lift 1 y) (tor 1 w one_n hwn) (tor 1 y one_n hyn)
  have hA := GlobalTheory.SiegelTypings.weilIs_mul hA2 hPL h11 h21
  have hB := GlobalTheory.SiegelTypings.weilIs_mul hA2 hPL hF h22
  rw [liftSq_mul, _root_.mul_one, _root_.one_mul] at hA hB
  have hs := GlobalTheory.CommPairing.weilIs_symm hPL (GlobalTheory.SiegelTypings.weilIs_mul hA2 hPL
    (GlobalTheory.CommPairing.weilIs_symm hPL hA) (GlobalTheory.CommPairing.weilIs_symm hPL hB))
  rw [liftSq_mul, _root_.mul_one, _root_.one_mul] at hs
  have hd := GlobalTheory.T.weilPairing_diagonal_pullback_eq S o.A o.P o.ab hPL _ (Over.mk x) w y _ _ hs hgeo
  have e11 := (GlobalTheory.T.weilPairing_birigidified_trivial_on_axes S o.A o.P o.ab hPL o.rig₁ o.rig₂ _ (Over.mk x) w y c11).1 h11
  have e22 := (GlobalTheory.T.weilPairing_birigidified_trivial_on_axes S o.A o.P o.ab hPL o.rig₁ o.rig₂ _ (Over.mk x) w y c22).2 h22
  have e21 := GlobalTheory.T.commutatorPairing_swap_eq_of_swap_invariant S o.A o.P o.ab hPL o.symm _ (Over.mk x) w y c21 F h21 hF
  rw [e11, e22, e21] at hd
  have hF2 : F ^ 2 = unitOn (I.ζ n₀ ^ (2 * ((c : ℤ) * D.EF x₁ x₂))) := by
    rw [← hEF, ← hd]; group

  have hζ : I.ζ n₀ ^ n₀ = 1 := (I.ζ_prim n₀ hn0 hjp).pow_eq_one
  have hz : ∀ z : ℤ, I.ζ n₀ ^ ((n₀ : ℤ) * z) = 1 := fun z => by
    rw [zpow_mul, zpow_natCast, hζ, one_zpow]
  have hmcZ : (m : ℤ) * c = (k : ℤ) ^ 2 := by exact_mod_cast hmc
  have hnZ : (n₀ : ℤ) = j * (k : ℤ) ^ 2 := by rw [hn₀]; push_cast; ring
  have uPow : ∀ (a : Kˣ) (n : ℕ), unitOn (a ^ n) = unitOn a ^ n := fun a n => map_pow (Units.map _) a n
  have uOne : unitOn (1 : Kˣ) = 1 := map_one (Units.map _)
  have hpw : ∀ t : ℕ, F ^ (2 * t) = unitOn (I.ζ n₀ ^ (2 * ((c : ℤ) * D.EF x₁ x₂) * (t : ℤ))) := fun t => by
    rw [pow_mul, hF2, ← uPow, ← zpow_natCast, ← zpow_mul]
  rcases hjpar with ⟨i, hi⟩ | hodd
  · have e : j * m = 2 * (i * m) := by rw [hi]; ring
    rw [hu', e, hpw]
    have ex' : 2 * ((c : ℤ) * D.EF x₁ x₂) * ((i * m : ℕ) : ℤ) = (n₀ : ℤ) * D.EF x₁ x₂ := by
      rw [hnZ, ← hmcZ, hi]; push_cast; ring
    rw [ex', hz, uOne]
  · have h2 : u ^ 2 = 1 := by
      rw [hu', ← pow_mul, Nat.mul_comm, hpw]
      have ex' : 2 * ((c : ℤ) * D.EF x₁ x₂) * ((j * m : ℕ) : ℤ) = (n₀ : ℤ) * (2 * D.EF x₁ x₂) := by
        rw [hnZ, ← hmcZ]; push_cast; ring
      rw [ex', hz, uOne]
    have hFn : F ^ n₀ = 1 := GlobalTheory.SiegelTypings.weil_pow_eq_one hA2 hPL (tor w 1 hwn one_n) hF
    have hn : u ^ n₀ = 1 := by rw [hu', ← pow_mul, Nat.mul_comm, pow_mul, hFn, one_pow]
    have hg := pow_gcd_eq_one.2 ⟨h2, hn⟩
    rwa [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.2 hodd), pow_one] at hg

end GlobalTheory.UPel.HT.Hecke
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_heckePoints_geometric_eq_one : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h₁ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ h₂ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (β : R →+* K), x ≫ s = spMap β → ∀ u : Γ((Over.mk x).left, ⊤)ˣ, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (toUnit (Over.mk x) ≫ (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A)) (toUnit (Over.mk x) ≫ (lift 1 h₂ : 𝟙_ (Over S) ⟶ G2 o.A)) u → u = 1 := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.weilIs_heckeSub_geom) | (exact GlobalTheory.UPel.HT.Hecke.weilIs_heckeSub_geom) | (intros; apply GlobalTheory.UPel.HT.Hecke.weilIs_heckeSub_geom <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Hecke

theorem weilIs_heckeSub_one : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h₁ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ h₂ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 h₂) 1 := by
  intro p _ D R _ b g c k N hc hk hN hNp hEF hg hck S s o h₁ hh₁ h₂ hh₂
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_commutatorPairing_value_heckePoints p D R b g c k N hc hk hN hNp hEF hg hck S s o h₁ hh₁ h₂ hh₂
  have hQ : (lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o.isLB _ _
  have hA2 : IsAbelianScheme (G2 o.A) :=
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have h1 : u = 1 := by
    refine GlobalTheory.T.scheme_rootOfUnity_eq_one_of_geometric_points R S s k u (b.unit k hk)
      (GlobalTheory.T.commutatorPairing_heckePoints_pow_eq_one p D R b g c k N hc hk hN hNp hEF hg hck S s o h₁ hh₁ h₂ hh₂ u hu) ?_
    intro K _ _ x β hx
    have hp := GlobalTheory.CommPairing.weilIs_pull (A := G2 o.A) GlobalTheory.globalFns_holds hA2 hQ (toUnit (Over.mk x)) hu
    exact GlobalTheory.T.weilPairing_heckePoints_geometric_eq_one p D R b g c k N hc hk hN hNp hEF hg hck S s o h₁ hh₁ h₂ hh₂ K x β hx _ hp
  subst h1
  exact hu

end GlobalTheory.UPel.HT.Hecke
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeSections_isotropic_commutatorPairing_linearMap : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h₁ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ h₂ ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift h₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 h₂) 1 := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.weilIs_heckeSub_one) | (exact GlobalTheory.UPel.HT.Hecke.weilIs_heckeSub_one) | (intros; apply GlobalTheory.UPel.HT.Hecke.weilIs_heckeSub_one <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem GlobalTheory.UPel.HT.Hecke.exists_descent_bundle_power_hecke_quotient : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover (GlobalTheory.UPel.HT.Hecke.heckeSub o g N) (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∃ P₀ : LB (G2 A').left, P₀.IsLB ∧ LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) (P₀.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) := by
  intro p _ D R _ b g c k N hc hk hN hNp hEF hg hck S s o A' _ _ ψ hA' hψ hGal
  obtain ⟨u, hu, hcoc⟩ := GlobalTheory.T.exists_linearisation_birigidifiedPower_isotropicSections S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ (k ^ 2 / c)
    (GlobalTheory.UPel.HT.Hecke.heckeSub o g N)
    (fun h hh => (GlobalTheory.T.heckeSections_linearSimilitude_mem_kernel_polarisation p D R b g c k N hc hk hN hNp hEF hg hck S s o h hh).1)
    (fun h hh => (GlobalTheory.T.heckeSections_linearSimilitude_mem_kernel_polarisation p D R b g c k N hc hk hN hNp hEF hg hck S s o h hh).2)
    (GlobalTheory.T.heckeSections_isotropic_commutatorPairing_linearMap p D R b g c k N hc hk hN hNp hEF hg hck S s o)
  have hGC := GlobalTheory.T.isGaloisCover_prod_sq2_of_isGaloisCover S o.A A' (GlobalTheory.UPel.HT.Hecke.heckeSub o g N) ψ hψ hGal
  obtain ⟨M, hM, hiso⟩ := GlobalTheory.LinDescent.exists_descent_of_isGaloisCover _ _ (GlobalTheory.UPel.HT.Hecke.sq2 ψ) _ _
    (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) hGC (DVR.linComb_isLB _ o.isLB _ _) u hu hcoc
  exact ⟨M, hM, hiso⟩
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descent_bundle_power_hecke_quotient' : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover (GlobalTheory.UPel.HT.Hecke.heckeSub o g N) (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∃ P₀ : LB (G2 A').left, P₀.IsLB ∧ LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) (P₀.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.exists_descent_bundle_power_hecke_quotient) | (exact GlobalTheory.UPel.HT.Hecke.exists_descent_bundle_power_hecke_quotient) | (intros; apply GlobalTheory.UPel.HT.Hecke.exists_descent_bundle_power_hecke_quotient <;> assumption)
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Hecke

theorem exists_pol_translate : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (act' : OActN D.O A') (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover (GlobalTheory.UPel.HT.Hecke.heckeSub o g N) (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') → ∃ P' : LB (G2 A').left, P'.IsLB ∧ (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) ∧ (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) ∧ LBIso P' (P'.pull (lift (snd A' A') (fst A' A')).left) ∧ Out.RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) ∧ (∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x ^ e = 1) ∧ (∀ c' : D.O, LBIso (P'.pull (lift (fst A' A' ≫ act'.act c') (snd A' A')).left) (P'.pull (lift (fst A' A') (snd A' A' ≫ act'.act (D.star c').unop)).left)) ∧ LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) := by
  intro p _ D R _ b g c k N hc hk hN hNp hEF hg hck S s o A' _ _ act' ψ hA' hψ hG hact
  obtain ⟨P₀, hP₀, w₀⟩ := GlobalTheory.T.exists_descent_bundle_power_hecke_quotient' p D R b g c k N hc hk hN hNp hEF hg hck S s o A' ψ hA' hψ hG
  obtain ⟨P', hP', r1, r2, w⟩ := GlobalTheory.T.exists_birigidified_bundle_of_descent p D R b (N * k) S s o A' ψ hψ _ P₀ hP₀ w₀
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.coprime_zero_left _ |>.1 hk)
  have hk2 : 0 < k ^ 2 := by positivity
  have hc0 : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; rw [zero_dvd_iff] at hck; omega)
  have hm1 : 1 ≤ k ^ 2 / c := Nat.div_pos (Nat.le_of_dvd hk2 hck) hc0
  have hmp : (k ^ 2 / c).Coprime p :=
    Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hck) (hk.pow_left 2)
  exact ⟨P', hP', r1, r2,
    GlobalTheory.T.descended_birigidified_bundle_symmetric p D R b (N * k) S s o A' ψ _ hA' hψ hG _ P' hP' w r1 r2,
    GlobalTheory.T.relAmple_diagonal_descended_bundle_galois_cover p D R b (N * k) S s o A' ψ _ hA' hψ hG _ hm1 P' hP' w,
    GlobalTheory.T.descendedBundle_kernel_killed_by_integer_prime_to_p p D R b (N * k) S s o A' ψ _ hA' hψ hG _ hmp P' hP' w,
    GlobalTheory.T.rosati_involution_of_galois_isogeny_descent p D R b (N * k) S s o A' act' ψ _ hA' hψ hG hact _ P' hP' w r1 r2, w⟩

end GlobalTheory.UPel.HT.Hecke
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hecke_translate_polarisation_bundle : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (act' : OActN D.O A') (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover (GlobalTheory.UPel.HT.Hecke.heckeSub o g N) (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') → ∃ P' : LB (G2 A').left, P'.IsLB ∧ (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) ∧ (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) ∧ LBIso P' (P'.pull (lift (snd A' A') (fst A' A')).left) ∧ Out.RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) ∧ (∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x ^ e = 1) ∧ (∀ c' : D.O, LBIso (P'.pull (lift (fst A' A' ≫ act'.act c') (snd A' A')).left) (P'.pull (lift (fst A' A') (snd A' A' ≫ act'.act (D.star c').unop)).left)) ∧ LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.exists_pol_translate) | (exact GlobalTheory.UPel.HT.Hecke.exists_pol_translate) | (intros; apply GlobalTheory.UPel.HT.Hecke.exists_pol_translate <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tateSimilitude_hecke_translate_geometric : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (act' : OActN D.O A') (ψ : o.A ⟶ A'), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover (GlobalTheory.UPel.HT.Hecke.heckeSub o g N) (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') → ∀ P' : LB (G2 A').left, P'.IsLB → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (β : R →+* κ), x ≫ s = spMap β → ∃ I : TateIsoO D κ (Over.mk x ⟶ A') (fun c g => g ≫ act'.act c) (fun n g g' z => Out.WeilIs A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ (o.eta (g y) ≫ ψ) = I.ev N y := by
  first | exact @GlobalTheory.UPel.HT.Hecke.TateTransl.exists_tateIsoO_transl | exact GlobalTheory.UPel.HT.Hecke.TateTransl.exists_tateIsoO_transl | (intros; apply GlobalTheory.UPel.HT.Hecke.TateTransl.exists_tateIsoO_transl <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.UPel.HT.Hecke

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem exists_isHecke : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∃ (o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsHecke g c k N o o' ψ := by
  intro p _ D R _ b g c k N hc hk hN hNp hEF hg hck S s o
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hk; exact (Fact.out : p.Prime).one_lt.ne' hk)
  have hN0 : 0 < N := by omega
  obtain ⟨hfin, hfree⟩ := GlobalTheory.UPel.HT.Hecke.heckeSub_finite_free p D R b g k N hk0 hN0 hk hNp S s o
  obtain ⟨A', _, _, ψ, hA', hψ, hgal⟩ := GlobalTheory.TranslQuotient.exists_quotient S o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left)
    (heckeSub o g N) o.ab (pull_isLB o.isLB _) o.ample hfin hfree
  have hepi : Epi ψ := by
    have := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hgal
    exact (Over.forget S).epi_of_epi_map this
  have kill : ∀ h ∈ heckeSub o g N, h ≫ ψ = 1 := fun h hh =>
    comp_eq_one_of_transl ψ h (hgal.inv ⟨h, hh⟩)
  have stab : ∀ c' : D.O, ∀ h ∈ heckeSub o g N, h ≫ o.act.act c' ∈ heckeSub o g N := by
    rintro c' _ ⟨x, rfl⟩
    refine ⟨c' • x, ?_⟩
    rw [← o.eta_lin, map_smul, smul_comm]
  choose actf hactf using fun c' : D.O => GlobalTheory.UPel.HT.Hecke.exists_desc_endo S o.A A' (heckeSub o g N) ψ hψ hgal (o.act.act c') (o.act.hom c') (stab c')
  let act' : OActN D.O A' :=
    { act := actf
      hom := fun c' => (hactf c').1
      one := by
        rw [← cancel_epi ψ, (hactf 1).2, o.act.one, Category.id_comp, Category.comp_id]
      mul := fun b' c' => by
        rw [← cancel_epi ψ, (hactf _).2, o.act.mul, Category.assoc, ← (hactf b').2, ← Category.assoc,
          ← (hactf c').2, Category.assoc]
      add := fun b' c' => by
        rw [← cancel_epi ψ, (hactf _).2, o.act.add, mul_comp, comp_mul, (hactf _).2, (hactf _).2] }
  have hcomp : ∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c' := fun c' => ((hactf c').2).symm
  obtain ⟨P', hP', r1, r2, hsym, hamp, hker, hros, hpull⟩ :=
    GlobalTheory.T.exists_hecke_translate_polarisation_bundle p D R b g c k N hc hk hN hNp hEF hg hck S s o A' act' ψ hA' hψ hgal hcomp
  obtain ⟨hlie, hlieR⟩ := GlobalTheory.UPel.HT.EtaleLie.lie_of_etale p D R b (N * k) S s o A' act' ψ _ _ hA' hψ hgal hcomp
  have hgeom := GlobalTheory.T.exists_tateSimilitude_hecke_translate_geometric p D R b g c k N hc hk hN hNp hEF hg hck S s o A' act' ψ hA' hψ hgal hcomp P' hP' r1 r2 hpull
  let o' : Obj b N s :=
    { A := A'
      ab := hA'
      act := act'
      P := P'
      isLB := hP'
      rig₁ := r1
      rig₂ := r2
      symm := hsym
      ample := hamp
      kerP := hker
      rosati := hros
      lie := hlie
      lieRank := hlieR
      eta := fun x => o.eta (g x) ≫ ψ
      eta_add := fun x y => by rw [map_add, o.eta_add, mul_comp]
      eta_lin := fun c' x => by
        show o.eta (g (c' • x)) ≫ ψ = (o.eta (g x) ≫ ψ) ≫ act'.act c'
        rw [map_smul, o.eta_lin, Category.assoc, hcomp, Category.assoc]
      eta_ker := fun x => by rw [map_nsmul]; exact kill _ (mem_heckeSub o g N x)
      geom := hgeom }
  exact ⟨o', ψ, hψ, hcomp, fun x => rfl, hgal, ⟨hpull⟩, hck⟩

end GlobalTheory.UPel.HT.Hecke
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primeToP_hecke_translate_harrisTaylor : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∃ (o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsHecke g c k N o o' ψ := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.exists_isHecke) | (exact GlobalTheory.UPel.HT.Hecke.exists_isHecke) | (intros; apply GlobalTheory.UPel.HT.Hecke.exists_isHecke <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

namespace GlobalTheory.UPel.HT.Hecke

theorem exists_isHeckeMap : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R]
    (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p →
    (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 →
    ∀ (M : Model b N) (M' : Model b (N * k)), ∃ π : M'.X ⟶ M.X, IsHeckeMap g c k N M.toRepFam M'.toRepFam π := by
  intro p _ D R _ _ b g c k N hc hk hN hNp hEF hg hck M M'
  obtain ⟨o', ψ, hψ⟩ := GlobalTheory.T.exists_primeToP_hecke_translate_harrisTaylor p D R b g c k N hc hk hN hNp hEF hg hck M'.X M'.s M'.univ
  obtain ⟨π, ⟨hπ, hm⟩, -⟩ := M.toRepFam.rep M'.X M'.s o'
  exact ⟨π, hπ, o', ψ, hψ, hm⟩

end GlobalTheory.UPel.HT.Hecke
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeMap_harrisTaylorIntegralModels : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (M : Model b N) (M' : Model b (N * k)), ∃ π : M'.X ⟶ M.X, IsHeckeMap g c k N M.toRepFam M'.toRepFam π := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.exists_isHeckeMap) | (exact GlobalTheory.UPel.HT.Hecke.exists_isHeckeMap) | (intros; apply GlobalTheory.UPel.HT.Hecke.exists_isHeckeMap <;> assumption)
end
