import Mathlib
import GroundTheory.PAdicHodge.BCrisNewtonLift
import GroundTheory.PAdicHodge.AInfGalois
import GroundTheory.PAdicHodge.AInfXi
import GroundTheory.PAdicHodge.TiltAlgClosed
import GroundTheory.PAdicHodge.TateCpTwist
import GroundTheory.PAdicHodge.SlopeDescentFixed
import GroundTheory.PAdicHodge.ExtRobbaIsoLift
import GroundTheory.PAdicHodge.ExtRobbaTrivialUnits
import GroundTheory.PAdicHodge.BCrisEigenWitt

section
set_option maxSynthPendingDepth 1

noncomputable section

open WittVector

namespace GroundTheory.PAdicHodge
namespace PhiGamma

variable (p : ℕ) [hp : Fact p.Prime]

abbrev Ob : Type _ := PreTilt (normInteger ℂ_[p]) p

abbrev Cb : Type _ :=
  Tilt ℂ_[p] NormedField.valuation (normInteger ℂ_[p]) normInteger_integers p

abbrev WC : Type _ := WittVector p (Cb p)

instance : IsAlgClosed (Cb p) := isAlgClosed_tilt

def toWC : AInf ℂ_[p] p →+* WC p := WittVector.map (algebraMap (Ob p) (Cb p))

theorem toWC_coeff (x : AInf ℂ_[p] p) (n : ℕ) :
    (toWC p x).coeff n = algebraMap (Ob p) (Cb p) (x.coeff n) :=
  WittVector.map_coeff _ x n

variable {p} {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem preTiltMap_congr {f g : ℂ_[p] →+* ℂ_[p]} (hf : ∀ x, ‖f x‖ = ‖x‖) (hg : ∀ x, ‖g x‖ = ‖x‖)
    (h : f = g) : preTiltMap p f hf = preTiltMap p g hg := by
  subst h; rfl

def galTilt (σ : Gal(PadicAlgCl p/K)) : Cb p →+* Cb p :=
  tiltMap p (galCp σ : ℂ_[p] →+* ℂ_[p]) (AInf.norm_galCp_toRingHom σ)

def galPreTilt (σ : Gal(PadicAlgCl p/K)) : Ob p →+* Ob p :=
  preTiltMap p (galCp σ : ℂ_[p] →+* ℂ_[p]) (AInf.norm_galCp_toRingHom σ)

theorem galTilt_algebraMap (σ : Gal(PadicAlgCl p/K)) (x : Ob p) :
    galTilt σ (algebraMap (Ob p) (Cb p) x) = algebraMap (Ob p) (Cb p) (galPreTilt σ x) :=
  tiltMap_algebraMap _ _ x

theorem norm_galTilt (σ : Gal(PadicAlgCl p/K)) (x : Cb p) : ‖galTilt σ x‖ = ‖x‖ :=
  norm_tiltMap _ _ x

theorem galPreTilt_one (x : Ob p) : galPreTilt (1 : Gal(PadicAlgCl p/K)) x = x := by
  have h : (galCp (1 : Gal(PadicAlgCl p/K)) : ℂ_[p] →+* ℂ_[p]) = RingHom.id ℂ_[p] := by
    rw [galCp_one]; rfl
  have key := AInf.preTiltMap_id (K := ℂ_[p]) (p := p) x
  rw [galPreTilt, preTiltMap_congr _ (fun _ => rfl) h]
  exact key

theorem galPreTilt_mul (σ τ : Gal(PadicAlgCl p/K)) (x : Ob p) :
    galPreTilt (σ * τ) x = galPreTilt σ (galPreTilt τ x) := by
  have h : (galCp (σ * τ) : ℂ_[p] →+* ℂ_[p]) =
      (galCp σ : ℂ_[p] →+* ℂ_[p]).comp (galCp τ : ℂ_[p] →+* ℂ_[p]) := by
    rw [galCp_mul]; rfl
  rw [galPreTilt, galPreTilt, galPreTilt, ← RingHom.comp_apply, ← preTiltMap_comp,
    preTiltMap_congr _ (norm_comp_eq (AInf.norm_galCp_toRingHom τ) (AInf.norm_galCp_toRingHom σ)) h]

theorem galTilt_one (x : Cb p) : galTilt (1 : Gal(PadicAlgCl p/K)) x = x := by
  have : galTilt (1 : Gal(PadicAlgCl p/K)) = RingHom.id (Cb p) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (Ob p)) (RingHom.ext fun a => ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply, galTilt_algebraMap, galPreTilt_one,
      RingHom.id_apply]
  rw [this, RingHom.id_apply]

theorem galTilt_mul (σ τ : Gal(PadicAlgCl p/K)) (x : Cb p) :
    galTilt (σ * τ) x = galTilt σ (galTilt τ x) := by
  have : galTilt (σ * τ) = (galTilt σ).comp (galTilt τ) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (Ob p)) (RingHom.ext fun a => ?_)
    simp only [RingHom.comp_apply, galTilt_algebraMap, galPreTilt_mul]
  rw [this, RingHom.comp_apply]

instance instMulSemiringActionCb : MulSemiringAction Gal(PadicAlgCl p/K) (Cb p) where
  smul σ x := galTilt σ x
  one_smul x := galTilt_one x
  mul_smul σ τ x := galTilt_mul σ τ x
  smul_zero σ := map_zero (galTilt σ)
  smul_add σ := map_add (galTilt σ)
  smul_one σ := map_one (galTilt σ)
  smul_mul σ := map_mul (galTilt σ)

instance instMulSemiringActionOb : MulSemiringAction Gal(PadicAlgCl p/K) (Ob p) where
  smul σ x := galPreTilt σ x
  one_smul x := galPreTilt_one x
  mul_smul σ τ x := galPreTilt_mul σ τ x
  smul_zero σ := map_zero (galPreTilt σ)
  smul_add σ := map_add (galPreTilt σ)
  smul_one σ := map_one (galPreTilt σ)
  smul_mul σ := map_mul (galPreTilt σ)

theorem gal_smul_algebraMap_ob (σ : Gal(PadicAlgCl p/K)) (x : Ob p) :
    σ • algebraMap (Ob p) (Cb p) x = algebraMap (Ob p) (Cb p) (σ • x) :=
  galTilt_algebraMap σ x

def galW (σ : Gal(PadicAlgCl p/K)) : WC p →+* WC p := WittVector.map (galTilt σ)

theorem galW_coeff (σ : Gal(PadicAlgCl p/K)) (x : WC p) (n : ℕ) :
    (galW σ x).coeff n = σ • x.coeff n :=
  WittVector.map_coeff _ x n

theorem galW_one (x : WC p) : galW (1 : Gal(PadicAlgCl p/K)) x = x := by
  ext n
  rw [galW_coeff, one_smul]

theorem galW_mul (σ τ : Gal(PadicAlgCl p/K)) (x : WC p) :
    galW (σ * τ) x = galW σ (galW τ x) := by
  ext n
  rw [galW_coeff, galW_coeff, galW_coeff, mul_smul]

instance instMulSemiringActionWC : MulSemiringAction Gal(PadicAlgCl p/K) (WC p) where
  smul σ x := galW σ x
  one_smul x := galW_one x
  mul_smul σ τ x := galW_mul σ τ x
  smul_zero σ := map_zero (galW σ)
  smul_add σ := map_add (galW σ)
  smul_one σ := map_one (galW σ)
  smul_mul σ := map_mul (galW σ)

theorem gal_smul_wc_coeff (σ : Gal(PadicAlgCl p/K)) (x : WC p) (n : ℕ) :
    (σ • x).coeff n = σ • x.coeff n :=
  galW_coeff σ x n

theorem gal_smul_natCast (σ : Gal(PadicAlgCl p/K)) (n : ℕ) : σ • (n : WC p) = n :=
  map_natCast (galW σ) n

theorem gal_smul_frobenius (σ : Gal(PadicAlgCl p/K)) (x : WC p) :
    σ • WittVector.frobenius x = WittVector.frobenius (σ • x) := by
  ext n
  rw [gal_smul_wc_coeff, WittVector.frobenius_eq_map_frobenius, WittVector.map_coeff,
    WittVector.map_coeff, gal_smul_wc_coeff, frobenius_def, frobenius_def, smul_pow']

theorem gal_smul_frobeniusEquiv (σ : Gal(PadicAlgCl p/K)) (x : WC p) :
    σ • WittVector.frobeniusEquiv p (Cb p) x = WittVector.frobeniusEquiv p (Cb p) (σ • x) :=
  gal_smul_frobenius σ x

theorem toWC_gal_smul (σ : Gal(PadicAlgCl p/K)) (x : AInf ℂ_[p] p) :
    toWC p (σ • x) = σ • toWC p x := by
  ext n
  rw [toWC_coeff, gal_smul_wc_coeff, toWC_coeff, AInf.gal_smul_coeff, gal_smul_algebraMap_ob]
  rfl

end PhiGamma
end GroundTheory.PAdicHodge
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace WittTilt

open _root_.WittVector

section Frob

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p

theorem incl_frobeniusEquiv (x : AInf K p) :
    incl K p (WittVector.frobeniusEquiv p 𝒪♭ x) = WittVector.frobeniusEquiv p K♭ (incl K p x) := by
  ext n
  rw [incl_coeff, WittVector.frobeniusEquiv_coeff, WittVector.frobeniusEquiv_coeff, incl_coeff,
    map_pow]

theorem incl_frobeniusEquiv_symm (x : AInf K p) :
    incl K p ((WittVector.frobeniusEquiv p 𝒪♭).symm x) =
      (WittVector.frobeniusEquiv p K♭).symm (incl K p x) := by
  apply (WittVector.frobeniusEquiv p K♭).injective
  rw [RingEquiv.apply_symm_apply, ← incl_frobeniusEquiv, RingEquiv.apply_symm_apply]

variable (K p) in

def frob : (teichLift K p).TeichFrob where
  φ := WittVector.frobeniusEquiv p K♭
  a := 1
  red_φ x := by
    show (WittVector.frobeniusEquiv p K♭ x).coeff 0 = x.coeff 0 ^ p ^ 1
    rw [WittVector.frobeniusEquiv_coeff, pow_one]
  u := 1
  φ_π := by
    rw [mul_one]
    exact map_natCast (WittVector.frobeniusEquiv p K♭) p
  u_mem_int := one_mem _
  norm_red_u := by
    show ‖(1 : WittVector p K♭).coeff 0‖ = 1
    rw [WittVector.one_coeff_zero, norm_one]
  map_int := by
    rintro _ ⟨y, rfl⟩
    exact ⟨_, incl_frobeniusEquiv y⟩
  symm_map_int := by
    rintro _ ⟨y, rfl⟩
    exact ⟨_, incl_frobeniusEquiv_symm y⟩

theorem frob_φ_apply (x : WittVector p K♭) :
    (frob K p).φ x = WittVector.frobeniusEquiv p K♭ x := rfl

@[simp] theorem frob_a : (frob K p).a = 1 := rfl

@[simp] theorem frob_u : (frob K p).u = 1 := rfl

theorem frob_φ_incl (x : AInf K p) :
    (frob K p).φ (incl K p x) = incl K p (WittVector.frobeniusEquiv p 𝒪♭ x) :=
  (incl_frobeniusEquiv x).symm

theorem frob_φ_comp_incl :
    ((frob K p).φ : WittVector p K♭ →+* WittVector p K♭).comp (incl K p) =
      (incl K p).comp (WittVector.frobeniusEquiv p 𝒪♭ : AInf K p →+* AInf K p) :=
  RingHom.ext frob_φ_incl

theorem coeff_frob (x : WittVector p K♭) (n : ℕ) :
    (teichLift K p).coeff ((frob K p).φ x) n = (teichLift K p).coeff x n ^ p := by
  set T := teichLift K p
  set F := frob K p
  have hred : ∀ y, T.red (F.φ.toRingHom y) = frobenius K♭ p (T.red y) := fun y => by
    rw [frobenius_def]
    have := F.red_φ y
    rw [frob_a, pow_one] at this
    exact this
  have hπ : F.φ.toRingHom T.π = T.π * 1 := F.φ_π
  have h1 := T.map_partialSum F.φ.toRingHom (frobenius K♭ p) hred hπ x (n + 1)
  have h2 := T.map_sub_map_partialSum_mem F.φ.toRingHom hπ x (n + 1)
  refine (T.coeff_eq_of_mem (a := fun m => frobenius K♭ p (T.coeff x m)) ?_ n le_rfl).trans
    (by rw [frobenius_def])
  have e : T.finSum (fun m => frobenius K♭ p (T.coeff x m)) (n + 1) =
      F.φ.toRingHom (T.partialSum x (n + 1)) := by
    rw [h1]; simp [TeichLift.finSum]
  rw [e]; exact h2



end Frob

section Galois

open PhiGamma

variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

def galTiltEquiv (σ : Gal(PadicAlgCl p/K)) : Cb p ≃+* Cb p :=
  RingEquiv.ofRingHom (galTilt σ) (galTilt σ⁻¹)
    (RingHom.ext fun x => by
      rw [RingHom.comp_apply, ← galTilt_mul, mul_inv_cancel, galTilt_one, RingHom.id_apply])
    (RingHom.ext fun x => by
      rw [RingHom.comp_apply, ← galTilt_mul, inv_mul_cancel, galTilt_one, RingHom.id_apply])

def galWEquiv (σ : Gal(PadicAlgCl p/K)) : WC p ≃+* WC p :=
  RingEquiv.ofRingHom (galW σ) (galW σ⁻¹)
    (RingHom.ext fun x => by
      rw [RingHom.comp_apply, ← galW_mul, mul_inv_cancel, galW_one, RingHom.id_apply])
    (RingHom.ext fun x => by
      rw [RingHom.comp_apply, ← galW_mul, inv_mul_cancel, galW_one, RingHom.id_apply])

def galIso (σ : Gal(PadicAlgCl p/K)) : (teichLift ℂ_[p] p).TeichIso where
  ψ := galWEquiv σ
  g := galTiltEquiv σ
  red_ψ x := galW_coeff σ x 0
  ψ_π := gal_smul_natCast σ p
  norm_g c := norm_galTilt σ c

theorem galIso_ψ (σ : Gal(PadicAlgCl p/K)) (x : WC p) : (galIso σ).ψ x = σ • x := rfl


theorem TeichIso_eq {T : TeichLift p (Cb p) (WC p)} {G₁ G₂ : T.TeichIso}
    (hψ : ∀ x, G₁.ψ x = G₂.ψ x) (hg : ∀ c, G₁.g c = G₂.g c) : G₁ = G₂ := by
  obtain ⟨ψ₁, g₁, _, _, _⟩ := G₁
  obtain ⟨ψ₂, g₂, _, _, _⟩ := G₂
  obtain rfl : ψ₁ = ψ₂ := RingEquiv.ext hψ
  obtain rfl : g₁ = g₂ := RingEquiv.ext hg
  rfl

theorem galIso_mul (σ τ : Gal(PadicAlgCl p/K)) : galIso (σ * τ) = (galIso σ).comp (galIso τ) :=
  TeichIso_eq (fun x => galW_mul σ τ x) (fun c => galTilt_mul σ τ c)

theorem galIso_one : galIso (1 : Gal(PadicAlgCl p/K)) = TeichLift.TeichIso.refl :=
  TeichIso_eq (fun x => galW_one x) (fun c => galTilt_one c)

theorem galIso_frob (σ : Gal(PadicAlgCl p/K)) (x : WC p) :
    (galIso σ).ψ ((frob ℂ_[p] p).φ x) = (frob ℂ_[p] p).φ ((galIso σ).ψ x) :=
  gal_smul_frobeniusEquiv σ x

theorem galIso_incl (σ : Gal(PadicAlgCl p/K)) (x : AInf ℂ_[p] p) :
    (galIso σ).ψ (incl ℂ_[p] p x) = incl ℂ_[p] p (σ • x) :=
  (toWC_gal_smul σ x).symm

theorem galIso_mem_int (σ : Gal(PadicAlgCl p/K)) {x : WC p} (hx : x ∈ (teichLift ℂ_[p] p).int) :
    (galIso σ).ψ x ∈ (teichLift ℂ_[p] p).int := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨σ • y, (galIso_incl σ y).symm⟩

theorem galIso_tildeMap_mul (σ τ : Gal(PadicAlgCl p/K)) (x : (teichLift ℂ_[p] p).RobbaTilde) :
    (galIso (σ * τ)).tildeMap x = (galIso σ).tildeMap ((galIso τ).tildeMap x) := by
  rw [galIso_mul, TeichLift.TeichIso.tildeMap_comp]

theorem galIso_tildeMap_one (x : (teichLift ℂ_[p] p).RobbaTilde) :
    (galIso (1 : Gal(PadicAlgCl p/K))).tildeMap x = x := by
  rw [galIso_one, TeichLift.TeichIso.tildeMap_refl]

theorem galIso_tildeMap_tildeFrob (σ : Gal(PadicAlgCl p/K)) (x : (teichLift ℂ_[p] p).RobbaTilde) :
    (galIso σ).tildeMap ((frob ℂ_[p] p).tildeFrob x) =
      (frob ℂ_[p] p).tildeFrob ((galIso σ).tildeMap x) :=
  (galIso σ).tildeMap_tildeFrob (frob ℂ_[p] p) (galIso_frob σ) x

end Galois

section Unramified

open PhiGamma EigenWitt

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p
local notation "𝓣" => teichLift ℂ_[p] p
local notation "W̄" => WittVector p (Fpbar p)

variable (p) in

abbrev WFrac : Type := FractionRing (WittVector p (Fpbar p))

variable (p) in

def wittFpbarToWC : W̄ →+* WC p := (incl ℂ_[p] p).comp wittToAInf


theorem wittFpbarToWC_mem_int (w : W̄) : wittFpbarToWC p w ∈ (𝓣).int := ⟨_, rfl⟩

theorem wittFpbarToWC_coeff (w : W̄) (n : ℕ) :
    (wittFpbarToWC p w).coeff n = algebraMap 𝒪♭ (Cb p) (fpbarToPreTilt (w.coeff n)) := by
  rw [wittFpbarToWC, RingHom.comp_apply, incl_coeff, wittToAInf, WittVector.map_coeff]



theorem wittFpbarToWC_frobenius (w : W̄) :
    wittFpbarToWC p (WittVector.frobenius w) = (frob ℂ_[p] p).φ (wittFpbarToWC p w) := by
  ext n
  rw [frob_φ_apply, WittVector.frobeniusEquiv_coeff, wittFpbarToWC_coeff, wittFpbarToWC_coeff,
    WittVector.coeff_frobenius_charP, map_pow, map_pow]

theorem exists_eq_zpow_mul (x : WFrac p) (hx : x ≠ 0) :
    ∃ (n : ℤ) (u : W̄ˣ), x = (algebraMap W̄ (WFrac p) p) ^ n * algebraMap W̄ (WFrac p) u := by
  obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := W̄) x
  have ha : a ≠ 0 := by rintro rfl; simp at hx
  have hs : s ≠ 0 := by rintro rfl; simp at hx
  obtain ⟨m, ua, rfl⟩ := WittVector.exists_eq_pow_p_mul' a ha
  obtain ⟨k, us, rfl⟩ := WittVector.exists_eq_pow_p_mul' s hs
  refine ⟨(m : ℤ) - k, ua * us⁻¹, ?_⟩
  have hp0 : algebraMap W̄ (WFrac p) p ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective W̄ (WFrac p))).2 (WittVector.irreducible p).ne_zero
  have hus : algebraMap W̄ (WFrac p) (us : W̄) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective W̄ (WFrac p))).2 us.ne_zero
  rw [zpow_sub₀ hp0, zpow_natCast, zpow_natCast, Units.val_mul, map_mul, map_mul, map_mul, map_pow,
    map_pow]
  have : algebraMap W̄ (WFrac p) ((us⁻¹ : W̄ˣ) : W̄) = (algebraMap W̄ (WFrac p) (us : W̄))⁻¹ :=
    map_units_inv _ us
  rw [this]
  field_simp

theorem isUnit_wittFpbar_to_B (y : nonZeroDivisors W̄) :
    IsUnit ((algebraMap (WC p) (𝓣).B).comp (wittFpbarToWC p) y) := by
  obtain ⟨m, u, hu⟩ := WittVector.exists_eq_pow_p_mul' (y : W̄) (nonZeroDivisors.coe_ne_zero y)
  have hf : (algebraMap (WC p) (𝓣).B).comp (wittFpbarToWC p) (p : W̄) =
      algebraMap (WC p) (𝓣).B (𝓣).π := by
    rw [RingHom.comp_apply, map_natCast]; rfl
  rw [hu, map_mul, map_pow, hf]
  exact IsUnit.mul (IsUnit.pow _ (IsLocalization.Away.algebraMap_isUnit (𝓣).π)) (u.isUnit.map _)

variable (p) in

def wittFpbarToB : WFrac p →+* (𝓣).B :=
  IsLocalization.lift (M := nonZeroDivisors W̄) (isUnit_wittFpbar_to_B (p := p))

theorem wittFpbarToB_algebraMap (w : W̄) :
    wittFpbarToB p (algebraMap W̄ (WFrac p) w) = algebraMap (WC p) (𝓣).B (wittFpbarToWC p w) :=
  IsLocalization.lift_eq _ w

theorem wittFpbarToB_p : wittFpbarToB p (algebraMap W̄ (WFrac p) p) = (𝓣).πB := by
  rw [wittFpbarToB_algebraMap, map_natCast]; rfl



end Unramified

section Tilde

open PhiGamma EigenWitt

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "W̄" => WittVector p (Fpbar p)

theorem convAll_piB_zpow (n : ℤ) : (𝓣).ConvAll ((((𝓣).piB ^ n : ((𝓣).B)ˣ)) : (𝓣).B) := by
  have hpow : ∀ (b : (𝓣).B), (𝓣).ConvAll b → ∀ k : ℕ, (𝓣).ConvAll (b ^ k) := by
    intro b hb k
    induction k with
    | zero => rw [pow_zero]; simpa using (TeichLift.convAll_π_pow (T := 𝓣) 0)
    | succ k ih => rw [pow_succ]; exact ih.mul hb
  rcases n with k | k
  · rw [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val, TeichLift.piB_val]
    exact TeichLift.convAll_π_pow k
  · rw [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
    have : (((𝓣).piB⁻¹ : ((𝓣).B)ˣ) : (𝓣).B) = IsLocalization.Away.invSelf (𝓣).π :=
      Units.inv_eq_of_mul_eq_one_right (by rw [TeichLift.piB_val]; exact IsLocalization.Away.mul_invSelf _)
    rw [this]
    exact hpow _ TeichLift.convAll_invSelf _

theorem wittFpbarToB_zpow_mul (n : ℤ) (w : W̄) :
    wittFpbarToB p ((algebraMap W̄ (WFrac p) p) ^ n * algebraMap W̄ (WFrac p) w) =
      (((𝓣).piB ^ n : ((𝓣).B)ˣ) : (𝓣).B) * algebraMap (WC p) (𝓣).B (wittFpbarToWC p w) := by
  have hP : IsUnit (algebraMap W̄ (WFrac p) p) :=
    ((map_ne_zero_iff _ (IsFractionRing.injective W̄ (WFrac p))).2
      (WittVector.irreducible p).ne_zero).isUnit
  have e1 : (algebraMap W̄ (WFrac p) p) ^ n = ((hP.unit ^ n : (WFrac p)ˣ) : WFrac p) := by
    rw [Units.val_zpow_eq_zpow_val, IsUnit.unit_spec]
  have e2 : Units.map (wittFpbarToB p : WFrac p →* (𝓣).B) hP.unit = (𝓣).piB := by
    ext
    rw [Units.coe_map, IsUnit.unit_spec, MonoidHom.coe_coe, wittFpbarToB_p, TeichLift.piB_val]
  rw [map_mul, e1, wittFpbarToB_algebraMap, ← e2, ← map_zpow, Units.coe_map, MonoidHom.coe_coe]

theorem convAll_wittFpbarToB (x : WFrac p) : (𝓣).ConvAll (wittFpbarToB p x) := by
  by_cases hx : x = 0
  · rw [hx, map_zero]; exact TeichLift.convAll_zero
  obtain ⟨n, u, rfl⟩ := exists_eq_zpow_mul x hx
  rw [wittFpbarToB_zpow_mul]
  exact (convAll_piB_zpow n).mul
    (TeichLift.convAll_algebraMap_of_mem_int (wittFpbarToWC_mem_int (u : W̄)))

theorem wittFpbarToB_mem_Edag (x : WFrac p) : wittFpbarToB p x ∈ (𝓣).Edag :=
  (𝓣).Econ_le_Edag ⟨1 / 2, by norm_num, by norm_num⟩ (convAll_wittFpbarToB x _ (by norm_num) (by norm_num))

variable (p) in

def wittFpbarToEdag : WFrac p →+* (𝓣).Edag :=
  (wittFpbarToB p).codRestrict _ wittFpbarToB_mem_Edag

variable (p) in

def wittFpbarToTilde : WFrac p →+* (𝓣).RobbaTilde := (𝓣).edagToTilde.comp (wittFpbarToEdag p)

theorem wittFpbarToTilde_apply (x : WFrac p) :
    wittFpbarToTilde p x = (𝓣).edagToTilde ⟨wittFpbarToB p x, wittFpbarToB_mem_Edag x⟩ := rfl

theorem wittFpbarToTilde_eq_tildeOf (x : WFrac p) :
    wittFpbarToTilde p x = (𝓣).tildeOf (wittFpbarToB p x) (convAll_wittFpbarToB x) :=
  (𝓣).edagToTilde_apply _




theorem isUnit_frobenius_fractionField (y : nonZeroDivisors W̄) :
    IsUnit ((algebraMap W̄ (WFrac p)).comp WittVector.frobenius (y : W̄)) := by
  refine Ne.isUnit ((map_ne_zero_iff _ (IsFractionRing.injective W̄ (WFrac p))).2 fun h => ?_)
  apply nonZeroDivisors.coe_ne_zero y
  apply (WittVector.frobeniusEquiv p (Fpbar p)).injective
  rw [map_zero]
  exact h

variable (p) in

def frobFrac : WFrac p →+* WFrac p :=
  IsLocalization.lift (M := nonZeroDivisors W̄) (isUnit_frobenius_fractionField (p := p))

theorem frobFrac_algebraMap (w : W̄) :
    frobFrac p (algebraMap W̄ (WFrac p) w) = algebraMap W̄ (WFrac p) (WittVector.frobenius w) :=
  IsLocalization.lift_eq _ w

theorem wittFpbarToB_frobFrac (x : WFrac p) :
    wittFpbarToB p (frobFrac p x) = (frob ℂ_[p] p).toB (wittFpbarToB p x) := by
  have : (wittFpbarToB p).comp (frobFrac p) =
      ((frob ℂ_[p] p).toB : (𝓣).B →+* (𝓣).B).comp (wittFpbarToB p) :=
    IsLocalization.ringHom_ext (nonZeroDivisors W̄) (RingHom.ext fun w => by
      simp only [RingHom.comp_apply, frobFrac_algebraMap, wittFpbarToB_algebraMap,
        RingEquiv.coe_toRingHom, TeichLift.TeichFrob.toB_algebraMap, wittFpbarToWC_frobenius])
  exact RingHom.congr_fun this x

theorem tildeFrob_wittFpbarToTilde (x : WFrac p) :
    (frob ℂ_[p] p).tildeFrob (wittFpbarToTilde p x) = wittFpbarToTilde p (frobFrac p x) := by
  rw [wittFpbarToTilde_apply, TeichLift.TeichFrob.tildeFrob_edagToTilde, wittFpbarToTilde_apply]
  congr 1
  exact Subtype.ext (wittFpbarToB_frobFrac x).symm

theorem padicIntToWittFpbar_injective : Function.Injective (padicIntToWittFpbar (p := p)) :=
  (WittVector.map_injective _ (ZMod.castHom (dvd_refl p) (Fpbar p)).injective).comp
    (WittVector.equiv p).symm.injective

theorem isUnit_padicInt_to_wittFraction (y : nonZeroDivisors ℤ_[p]) :
    IsUnit ((algebraMap W̄ (WFrac p)).comp padicIntToWittFpbar (y : ℤ_[p])) :=
  Ne.isUnit ((map_ne_zero_iff _ (IsFractionRing.injective W̄ (WFrac p))).2
    ((map_ne_zero_iff _ padicIntToWittFpbar_injective).2 (nonZeroDivisors.coe_ne_zero y)))

variable (p) in

def padicToWFrac : ℚ_[p] →+* WFrac p :=
  IsLocalization.lift (M := nonZeroDivisors ℤ_[p]) (S := ℚ_[p]) (isUnit_padicInt_to_wittFraction (p := p))

theorem padicToWFrac_padicInt (z : ℤ_[p]) :
    padicToWFrac p (algebraMap ℤ_[p] ℚ_[p] z) = algebraMap W̄ (WFrac p) (padicIntToWittFpbar z) :=
  IsLocalization.lift_eq _ z

theorem frobFrac_padicToWFrac (q : ℚ_[p]) : frobFrac p (padicToWFrac p q) = padicToWFrac p q := by
  have : (frobFrac p).comp (padicToWFrac p) = padicToWFrac p :=
    IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p]) (RingHom.ext fun z => by
      show frobFrac p (padicToWFrac p (algebraMap ℤ_[p] ℚ_[p] z)) =
        padicToWFrac p (algebraMap ℤ_[p] ℚ_[p] z)
      rw [padicToWFrac_padicInt, frobFrac_algebraMap, frobenius_padicIntToWittFpbar])
  exact RingHom.congr_fun this q

variable (p) in

def padicToTilde : ℚ_[p] →+* (𝓣).RobbaTilde := (wittFpbarToTilde p).comp (padicToWFrac p)

theorem tildeFrob_padicToTilde (q : ℚ_[p]) :
    (frob ℂ_[p] p).tildeFrob (padicToTilde p q) = padicToTilde p q := by
  rw [padicToTilde, RingHom.comp_apply, tildeFrob_wittFpbarToTilde, frobFrac_padicToWFrac]

end Tilde

section Fixed

open PhiGamma EigenWitt Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "W̄" => WittVector p (Fpbar p)
local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p

theorem exists_zmod_of_pow_eq_self_field {E : Type*} [Field E] [CharP E p] {a : E} (ha : a ^ p = a) :
    ∃ b : ZMod p, ZMod.castHom (dvd_refl p) E b = a := by
  classical
  set P : (ZMod p)[X] := X ^ p - X with hP
  have hdeg : P.natDegree = p := by
    rw [hP, natDegree_sub_eq_left_of_natDegree_lt] <;> simp [hp.out.one_lt]
  have hroots : P.roots = Finset.univ.val := by
    have h := FiniteField.roots_X_pow_card_sub_X (ZMod p)
    rwa [ZMod.card] at h
  have hcard : Multiset.card P.roots = P.natDegree := by
    rw [hroots, hdeg, Finset.card_val, Finset.card_univ, ZMod.card]
  have hmap := roots_map_of_injective_of_card_eq_natDegree
    (ZMod.castHom (dvd_refl p) E).injective hcard
  have hne : (X ^ p - X : E[X]) ≠ 0 := by
    intro h
    have := congrArg natDegree h
    rw [natDegree_sub_eq_left_of_natDegree_lt (by simp [hp.out.one_lt]), natDegree_X_pow,
      natDegree_zero] at this
    exact hp.out.ne_zero this
  have hmem : a ∈ (P.map (ZMod.castHom (dvd_refl p) E)).roots := by
    rw [show P.map (ZMod.castHom (dvd_refl p) E) = X ^ p - X by simp [hP], mem_roots hne]
    simp [ha]
  rw [← hmap, Multiset.mem_map] at hmem
  obtain ⟨b, -, hb⟩ := hmem
  exact ⟨b, hb⟩

theorem exists_padicInt_of_frob_eq {u : WC p} (hu : (frob ℂ_[p] p).φ u = u) :
    ∃ z : ℤ_[p], wittFpbarToWC p (padicIntToWittFpbar z) = u := by
  have hc : ∀ n, ∃ b : ZMod p, ZMod.castHom (dvd_refl p) (Cb p) b = u.coeff n := fun n =>
    exists_zmod_of_pow_eq_self_field (by rw [← WittVector.frobeniusEquiv_coeff, ← frob_φ_apply, hu])
  choose b hb using hc
  refine ⟨WittVector.equiv p (WittVector.mk p b), ?_⟩
  ext n
  rw [wittFpbarToWC_coeff, ← hb n]
  simp only [padicIntToWittFpbar, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply, WittVector.map_coeff]
  exact RingHom.congr_fun (RingHom.ext_zmod ((algebraMap 𝒪♭ (Cb p)).comp
    (fpbarToPreTilt.comp (ZMod.castHom (dvd_refl p) (Fpbar p)))) (ZMod.castHom (dvd_refl p) (Cb p))) (b n)

theorem val_piB_zpow (n : ℤ) : (((𝓣).piB ^ n : ((𝓣).B)ˣ) : (𝓣).B) = (𝓣).πB ^ n := by
  rw [Units.val_zpow_eq_zpow_val, TeichLift.piB_val]

theorem tildeFrob_eq_self_iff (x : (𝓣).RobbaTilde) :
    (frob ℂ_[p] p).tildeFrob x = x ↔ ∃ q : ℚ_[p], x = padicToTilde p q := by
  refine ⟨fun hx => ?_, fun ⟨q, hq⟩ => hq ▸ tildeFrob_padicToTilde q⟩
  by_cases hx0 : x = 0
  · exact ⟨0, by rw [hx0, map_zero]⟩
  have hzφ : (frob ℂ_[p] p).φ ((𝓣).π * 1) = (𝓣).π * 1 := by
    rw [mul_one, (frob ℂ_[p] p).φ_π, frob_u, mul_one]
  obtain ⟨c, u, -, -, hφu, h, rfl⟩ := (frob ℂ_[p] p).exists_eq_zpow_mul_of_fixed
    (by rw [frob_a]; exact one_pos) (one_mem _) (by rw [map_one, norm_one]) hzφ hx0 hx
  obtain ⟨z, rfl⟩ := exists_padicInt_of_frob_eq hφu
  refine ⟨(p : ℚ_[p]) ^ c * algebraMap ℤ_[p] ℚ_[p] z, ?_⟩
  rw [padicToTilde, RingHom.comp_apply, wittFpbarToTilde_eq_tildeOf]
  apply (𝓣).tildeOf_congr
  rw [map_mul, map_zpow₀, map_natCast, padicToWFrac_padicInt, ← map_natCast (algebraMap W̄ (WFrac p)),
    wittFpbarToB_zpow_mul, val_piB_zpow, map_one, mul_one]


end Fixed

end WittTilt

end GroundTheory.PAdicHodge
end
end
