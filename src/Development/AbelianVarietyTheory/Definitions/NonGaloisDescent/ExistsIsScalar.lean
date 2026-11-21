import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GoodSetupCountEqZeroOffBadPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnivCharWithUnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SurjConj
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.RatDatOfReal

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF Vc Wc)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
open Formalism.L2.Host (embLL0)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lin

variable {R : Type} [CommRing R] [IsDomain R]

def Via (R : Type) [CommRing R] (_e : FractionRing R →+* ℂ) (A : Type) : Type := A

variable {e : FractionRing R →+* ℂ} {A : Type} [AddCommGroup A] [Module ℂ A]

instance : AddCommGroup (Via R e A) := inferInstanceAs (AddCommGroup A)
instance : Module (FractionRing R) (Via R e A) := Module.compHom A e
instance : Module R (Via R e A) := Module.compHom A (e.comp (algebraMap R (FractionRing R)))
instance : IsScalarTower R (FractionRing R) (Via R e A) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl

def Via.out (e : FractionRing R →+* ℂ) (A : Type) [AddCommGroup A] [Module ℂ A] : Via R e A →ₛₗ[e] A where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def Via.lat (L : Submodule (e.comp (algebraMap R (FractionRing R))).range A) : Submodule R (Via R e A) where
  carrier := {x | Via.out e A x ∈ L}
  add_mem' := L.add_mem
  zero_mem' := L.zero_mem
  smul_mem' c _ h := L.smul_mem ⟨_, c, rfl⟩ h

theorem Via.lat_fg {L : Submodule (e.comp (algebraMap R (FractionRing R))).range A} (h : L.FG) : (Via.lat L).FG := by
  obtain ⟨S, rfl⟩ := h
  refine ⟨S, le_antisymm (Submodule.span_le.2 fun x hx => Submodule.subset_span (M := A) hx) fun x hx => ?_⟩
  have key : ∀ y : A, y ∈ Submodule.span (e.comp (algebraMap R (FractionRing R))).range (S : Set A) →
      (y : Via R e A) ∈ Submodule.span R (M := Via R e A) (S : Set A) := fun y hy => by
    induction hy using Submodule.span_induction with
    | mem _ h => exact Submodule.subset_span h
    | zero => exact zero_mem _
    | add _ _ _ _ h1 h2 => exact add_mem h1 h2
    | smul c _ _ h1 =>
      obtain ⟨_, c, rfl⟩ := c
      exact Submodule.smul_mem _ c h1
  exact key x hx

variable {V : Type} [AddCommGroup V] [Module (FractionRing R) V] [Module R V] [IsScalarTower R (FractionRing R) V]

def inSpan (L : Submodule R V) : Submodule R (Submodule.span (FractionRing R) (L : Set V)) :=
  L.comap ((Submodule.span (FractionRing R) (L : Set V)).subtype.restrictScalars R)

theorem inSpan_fg {L : Submodule R V} (h : L.FG) : (inSpan L).FG := by
  refine Submodule.fg_of_fg_map_injective ((Submodule.span (FractionRing R) (L : Set V)).subtype.restrictScalars R)
    Subtype.val_injective ?_
  rwa [inSpan, Submodule.map_comap_eq_self fun x hx => ⟨⟨x, Submodule.subset_span hx⟩, rfl⟩]

theorem span_inSpan (L : Submodule R V) : Submodule.span (FractionRing R)
    (inSpan L : Set (Submodule.span (FractionRing R) (L : Set V))) = ⊤ := Submodule.span_span_coe_preimage

theorem finiteDimensional_span {L : Submodule R V} (h : L.FG) :
    FiniteDimensional (FractionRing R) (Submodule.span (FractionRing R) (L : Set V)) := by
  obtain ⟨S, rfl⟩ := h
  rw [Submodule.span_span_of_tower]
  exact FiniteDimensional.span_of_finite _ S.finite_toSet

theorem exists_lift {M : Type} [AddCommGroup M] [Module R M] (g : V →ₛₗ[e] A)
    (r : M →ₛₗ[e.comp (algebraMap R (FractionRing R))] A) (hr : Function.Injective r)
    (hdiv : ∀ a : R, a ≠ 0 → ∀ m : M, ∃ m', a • m' = m) :
    ∃ φ : V →ₗ[R] M, ∀ v, g v ∈ Set.range r → r (φ v) = g v := by
  let U : Submodule (FractionRing R) V :=
    { carrier := {v | g v ∈ Set.range r}
      zero_mem' := ⟨0, by rw [map_zero, map_zero]⟩
      add_mem' := by
        rintro _ _ ⟨x, hx⟩ ⟨y, hy⟩
        exact ⟨x + y, by rw [map_add, map_add, hx, hy]⟩
      smul_mem' := by
        rintro c v ⟨x, hx⟩
        obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := R) c
        have hd' := nonZeroDivisors.ne_zero hd
        obtain ⟨y, rfl⟩ := hdiv d hd' x
        refine ⟨a • y, ?_⟩
        rw [map_smulₛₗ, map_smulₛₗ, ← hx, map_smulₛₗ, smul_smul, RingHom.comp_apply, RingHom.comp_apply, ← map_mul,
          div_mul_cancel₀ _ (by simpa using hd')] }
  obtain ⟨p, hp⟩ := U.subtype.exists_leftInverse_of_injective U.ker_subtype
  choose s hs using fun u : U => u.2
  let ψ : U →ₗ[R] M :=
    { toFun := s
      map_add' := fun u u' => hr (by rw [map_add, hs, hs, hs, Submodule.coe_add, map_add])
      map_smul' := fun c u => hr (by
        rw [RingHom.id_apply, map_smulₛₗ, hs, hs, Submodule.coe_smul_of_tower, ← algebraMap_smul (FractionRing R) c,
          map_smulₛₗ]; rfl) }
  refine ⟨ψ ∘ₗ p.restrictScalars R, fun v hv => ?_⟩
  have : p v = ⟨v, hv⟩ := LinearMap.congr_fun hp ⟨v, hv⟩
  change r (s (p v)) = _
  rw [this, hs]

end Lin

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem divisible_baseChange (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (n : ℕ) (b : Bool) (k : ℕ) (a : X.Ok i k)
    (ha : a ≠ 0) (m : X.Ok i k ⊗[X.O i] Y.Fm i n b) : ∃ m', a • m' = m := by
  haveI := X.Ok_fin i k
  obtain ⟨d, hd, c, hc⟩ := (Algebra.IsIntegral.isIntegral (R := X.O i) a).isAlgebraic.exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero ha)
  have key : ∀ m : X.Ok i k ⊗[X.O i] Y.Fm i n b, ∃ m', d • m' = m := fun m => by
    induction m using TensorProduct.induction_on with
    | zero => exact ⟨0, smul_zero _⟩
    | add x y hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      exact ⟨x + y, smul_add _ _ _⟩
    | tmul z f =>
      refine ⟨z ⊗ₜ ((algebraMap (X.O i) (FractionRing (X.O i)) d)⁻¹ • f), ?_⟩
      rw [← TensorProduct.tmul_smul, ← algebraMap_smul (FractionRing (X.O i)) d, smul_inv_smul₀ (by simpa using hd)]
  obtain ⟨m', rfl⟩ := key m
  exact ⟨c • m', by rw [smul_smul, ← hc, algebraMap_smul]⟩

theorem finite_dvd_normProd (s : Finset (Pl D.host.E)) :
    {v : Pl D.host.E | ((normProd s : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((normProd s : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact Finset.prod_ne_zero_iff.2 fun v _ h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 hv

variable {ρ : Setup X} (hρ : ρ.Good) {Y : NExp D.R D.host D.what₂ D.LL0 N X} (rd : Rds Y ρ)

def Setup.LatFG (ρ : Setup X) : Prop := ∀ i j b k Q ψ, TwOK i k Q ψ → (ρ.mt i j b k Q ψ).FG

structure Setup.LevelOf (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) : Prop where
  U_eq : ∀ i j b g, ρ.eG i j b g ∈ (ρ.B i j b).G.P.H ↔ g ∈ Y.U
  psiU_eq : ∀ i j b (u : Y.U) hu,
    (((ρ.B i j b).G.P.chi ⟨ρ.eG i j b u, hu⟩ : ℂˣ) : ℂ) = ρ.e i b (Y.psiU i b u : (FractionRing (X.O i))ˣ)

namespace Model

structure RatDatum (i : X.Tw) (j : Fin D.R.m) (b : Bool) where
  s : Finset (Pl D.host.E)
  h : GA D (Vc D j)
  P : PolF D (Wc D j).rank (Vc D j).rank
  isDatum : ρ.IsDatum i j b s h P
  rat : ρ.theta i j b h P ∈ Set.range (rd i j b)

def Dat (i : X.Tw) : ℕ → Bool → Type
  | 0, _ => PEmpty
  | n + 1, b => (h : n < D.R.m) ×' RatDatum rd i ⟨n, h⟩ b

def th (i : X.Tw) : ∀ n b, Dat rd i n b → Y.Fm i n b
  | 0, _ => fun d => d.elim
  | _ + 1, _ => fun d => d.2.rat.choose

def lev (i : X.Tw) : ∀ n b, Dat rd i n b → Finset (Pl D.host.E)
  | 0, _ => fun d => d.elim
  | _ + 1, _ => fun d => (finite_dvd_normProd d.2.s).toFinset

def thPsi (i : X.Tw) : ∀ n b k (_ : Finset (Pl D.host.E)) (_ : G D.host.E N.Om →* (X.Ok i k)ˣ),
    Dat rd i n b → Set (X.Ok i k ⊗[X.O i] Y.Fm i n b)
  | 0, _, _, _, _ => fun d => d.elim
  | n + 1, b, k, Q, ψ => fun d => rdK (rd i ⟨n, d.1⟩ b) hρ k ⁻¹' ρ.gens i ⟨n, d.1⟩ b k Q ψ d.2.h d.2.P

open Classical in
def thU (i : X.Tw) : ∀ n b (Q : Finset (Pl D.host.E)) (M : ℕ), Dat rd i n b →
    Y.Fm i n b ⊗[X.O i] AddMonoidAlgebra (X.O i) (DelQM D.host (X.l i) Q M)
  | 0, _, _, _ => fun d => d.elim
  | n + 1, b, Q, M => fun d =>
    if h : InRange X i Q ∧ ∀ a, ρ.xi i ⟨n, d.1⟩ b Y Q M d.2.h d.2.P a ∈ Set.range (rd i ⟨n, d.1⟩ b) then
      grpSum Y (ρ.ch i) Q M fun a => (h.2 a).choose
    else 0

abbrev Amb (ρ : Setup X) (i : X.Tw) (n : ℕ) (b : Bool) (k : ℕ) : Type :=
  Via (X.Ok i k) (ρ.ek i b k) (Bridge.Gf (D.sp.V n) → PolF D (D.sp.W n).rank (D.sp.V n).rank)

open Classical in

def lat (ρ : Setup X) (i : X.Tw) : ∀ n b k (_ : Finset (Pl D.host.E)) (_ : G D.host.E N.Om →* (X.Ok i k)ˣ),
    Submodule (X.Ok i k) (Amb ρ i n b k)
  | 0, _, _, _, _ => ⊥
  | n + 1, b, k, Q, ψ => if h : n < D.R.m ∧ TwOK i k Q ψ then Via.lat (ρ.mt i ⟨n, h.1⟩ b k Q ψ) else ⊥

theorem lat_fg (hL : ρ.LatFG) (i : X.Tw) : ∀ n b k Q ψ, (lat ρ i n b k Q ψ).FG
  | 0, _, _, _, _ => Submodule.fg_bot
  | n + 1, b, k, Q, ψ => by
    rw [lat]
    split_ifs with h
    · exact Via.lat_fg (hL i ⟨n, h.1⟩ b k Q ψ h.2)
    · exact Submodule.fg_bot

abbrev MtV (ρ : Setup X) (i : X.Tw) (n : ℕ) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E))
    (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ) : Type :=
  Submodule.span (FractionRing (X.Ok i k)) (lat ρ i n b k Q ψ : Set (Amb ρ i n b k))

def rdV (ρ : Setup X) (i : X.Tw) (n : ℕ) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ) :
    MtV ρ i n b k Q ψ →ₛₗ[ρ.ek i b k] (Bridge.Gf (D.sp.V n) → PolF D (D.sp.W n).rank (D.sp.V n).rank) :=
  (Via.out _ _).comp (Submodule.subtype _)

variable (hF : ∀ i j b, Faithful (rd i j b))

include hF in
theorem exists_thP (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E))
    (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ) :
    ∃ φ : MtV ρ i ((j : ℕ) + 1) b k Q ψ →ₗ[X.Ok i k] X.Ok i k ⊗[X.O i] Y.Fm i ((j : ℕ) + 1) b,
      ∀ f, ρ.sum i j b k Q ψ (rdV ρ i _ b k Q ψ f) ∈ Set.range (rdK (rd i j b) hρ k) →
        rdK (rd i j b) hρ k (φ f) = ρ.sum i j b k Q ψ (rdV ρ i _ b k Q ψ f) :=
  exists_lift ((ρ.sum i j b k Q ψ).comp (rdV ρ i _ b k Q ψ)) (rdK (rd i j b) hρ k) ((hF i j b).injective_rdK hρ k)
    (divisible_baseChange Y i _ b k)

def thP (i : X.Tw) : ∀ n b k Q ψ, MtV ρ i n b k Q ψ →ₗ[X.Ok i k] X.Ok i k ⊗[X.O i] Y.Fm i n b
  | 0, _, _, _, _ => 0
  | n + 1, b, k, Q, ψ => if h : n < D.R.m then (exists_thP hρ rd hF i ⟨n, h⟩ b k Q ψ).choose else 0

include hF in
theorem thPsi_one (i : X.Tw) : ∀ n b k (d : Dat rd i n b),
    thPsi hρ rd i n b k ∅ 1 d = {(1 : X.Ok i k) ⊗ₜ[X.O i] th rd i n b d}
  | 0, _, _, d => d.elim
  | n + 1, b, k, d => by
    ext x
    rw [thPsi, Set.mem_preimage, Setup.gens_one, Set.mem_singleton_iff, Set.mem_singleton_iff,
      ← ((hF i ⟨n, d.1⟩ b).injective_rdK hρ k).eq_iff, rdK_tmul, map_one, one_smul, ← d.2.rat.choose_spec]
    rfl

end Model

variable (hF : ∀ i j b, Faithful (rd i j b)) (hL : ρ.LatFG)

def withSeries : NExp D.R D.host D.what₂ D.LL0 N X :=
  { Y with
    Dat := Model.Dat rd
    th := Model.th rd
    lev := Model.lev rd
    thPsi := Model.thPsi hρ rd
    thPsi_one := Model.thPsi_one hρ rd hF
    thU := Model.thU rd
    MtV := Model.MtV ρ
    acgMt := fun _ _ _ _ _ _ => inferInstance
    modMtK := fun _ _ _ _ _ _ => inferInstance
    modMtO := fun _ _ _ _ _ _ => inferInstance
    towMt := fun _ _ _ _ _ _ => inferInstance
    fdMt := fun i n b k Q ψ => finiteDimensional_span (Model.lat_fg hL i n b k Q ψ)
    MtLat := fun i n b k Q ψ => inSpan (Model.lat ρ i n b k Q ψ)
    MtLat_fg := fun i n b k Q ψ => inSpan_fg (Model.lat_fg hL i n b k Q ψ)
    MtLat_span := fun _ _ _ _ _ _ => span_inSpan _
    thP := Model.thP hρ rd hF }

def tieWithSeries (hU : ρ.LevelOf Y) : Comparison₂ hρ (Y := withSeries hρ rd hF hL) rd := fun i j b =>
  { supp := fun d => d.2.s
    cls := fun d => d.2.h
    coef := fun d => d.2.P
    rdV := Model.rdV ρ i _ b
    U_eq := hU.U_eq i j b
    psiU_eq := hU.psiU_eq i j b
    dat := fun d => d.2.isDatum
    dat_onto := fun s h P h1 h2 => ⟨⟨j.2, s, h, P, h1, h2⟩, rfl, rfl, rfl⟩
    lev_iff := fun _ _ => Set.Finite.mem_toFinset _
    th_eq := fun d => d.2.rat.choose_spec
    thPsi_iff := fun _ _ _ _ _ _ => Iff.rfl
    thU_eq := fun Q M d hQ x hx => by
      have h : InRange X i Q ∧ ∀ a, ρ.xi i j b Y Q M d.2.h d.2.P a ∈ Set.range (rd i j b) := ⟨hQ, fun a => ⟨x a, hx a⟩⟩
      refine (dif_pos h).trans (congrArg (grpSum Y (ρ.ch i) Q M) (funext fun a => (hF i j b).injective ?_))
      exact (h.2 a).choose_spec.trans (hx a).symm
    thU_off := fun _ _ _ h => dif_neg h
    rdV_inj := fun _ _ _ _ => Subtype.val_injective
    mtLat_iff := fun k Q ψ h F => by
      have e : Model.lat ρ i ((j : ℕ) + 1) b k Q ψ = Via.lat (ρ.mt i j b k Q ψ) := dif_pos ⟨j.2, h⟩
      refine ⟨fun hF => ?_, fun ⟨f, hf, e'⟩ => ?_⟩
      · have h1 : F ∈ Model.lat ρ i ((j : ℕ) + 1) b k Q ψ := e ▸ hF
        exact ⟨⟨F, Submodule.subset_span h1⟩, h1, rfl⟩
      · have h1 : f.1 ∈ Model.lat ρ i ((j : ℕ) + 1) b k Q ψ := hf
        exact e' ▸ e.le h1
    thP_eq := fun k Q ψ _ f hf => by
      have e : Model.thP hρ rd hF i ((j : ℕ) + 1) b k Q ψ = (Model.exists_thP hρ rd hF i j b k Q ψ).choose := dif_pos j.2
      exact (congrArg (fun φ => rdK (rd i j b) hρ k (φ f)) e).trans ((Model.exists_thP hρ rd hF i j b k Q ψ).choose_spec f hf) }

end GlobalTheory.SeriesTie

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF Vc Wc)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
open Formalism.MainNotions.NAdm (TWSet AdmQ)
open GlobalTheory.UnivChar (IsUnivChar withUnivChar)
open Formalism.L2.Host (embLL0)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem exists_end_reads {K M A ι : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup A] [Module ℂ A] {e : K →+* ℂ}
    (r : M →ₛₗ[e] A) (hr : Function.Injective r) (S : ι → A →ₗ[ℂ] A) :
    ∃ T : Module.End K M, ∀ f, (∃ g, ∀ a, r g = S a (r f)) → ∀ a, r (T f) = S a (r f) := by
  rcases isEmpty_or_nonempty ι with h | ⟨⟨a₀⟩⟩
  · exact ⟨0, fun _ _ a => isEmptyElim a⟩
  let U : Submodule K M :=
    { carrier := {f | ∃ g, ∀ a, r g = S a (r f)}
      zero_mem' := ⟨0, fun a => by rw [map_zero, map_zero]⟩
      add_mem' := by
        rintro _ _ ⟨x, hx⟩ ⟨y, hy⟩
        exact ⟨x + y, fun a => by rw [map_add, map_add, map_add, hx a, hy a]⟩
      smul_mem' := by
        rintro c v ⟨x, hx⟩
        exact ⟨c • x, fun a => by rw [map_smulₛₗ, map_smulₛₗ, map_smul, hx a]⟩ }
  obtain ⟨p, hp⟩ := U.subtype.exists_leftInverse_of_injective U.ker_subtype
  choose s hs using fun u : U => u.2
  let ψ : U →ₗ[K] M :=
    { toFun := s
      map_add' := fun u u' => hr (by rw [map_add, hs _ a₀, hs _ a₀, hs _ a₀, Submodule.coe_add, map_add, map_add])
      map_smul' := fun c u => hr (by
        rw [RingHom.id_apply, map_smulₛₗ, hs _ a₀, hs _ a₀, Submodule.coe_smul, map_smulₛₗ, map_smul]) }
  refine ⟨ψ ∘ₗ p, fun v hv a => ?_⟩
  have : p v = ⟨v, hv⟩ := LinearMap.congr_fun hp ⟨v, hv⟩
  change r (s (p v)) = _
  rw [this, hs _ a]

namespace Setup

variable (ρ : Setup X) (i : X.Tw) (j : Fin D.R.m) (b : Bool)

structure IsHeckeDatum (k : ℕ) (P : Pl D.host.E) (α : GA D (Wc D j)) (R : Finset (GA D (Wc D j))) (z : (AE D)ˣ) : Prop where
  elt : Links.IsHeckeAt (Wc D j) P k α
  reps : Bridge.IsDC (ρ.levK i j b) α R
  det : IsDetAt (idemAt P) (Wc D j) α z

def hecke (k : ℕ) (P : Pl D.host.E) (R : Finset (GA D (Wc D j))) (z : (AE D)ˣ) :
    (GA D (Wc D j) → ℂ) →ₗ[ℂ] (GA D (Wc D j) → ℂ) :=
  ((((ρ.B i j b).mu z : Circle) : ℂ)⁻¹ * (((normV P : ℕ) : ℂ) ^ (k * ((Vc D j).rank / 2)))⁻¹) •
    ∑ γ ∈ R, LinearMap.funLeft ℂ ℂ fun x => x * γ

theorem hecke_apply (k : ℕ) (P : Pl D.host.E) (R : Finset (GA D (Wc D j))) (z : (AE D)ˣ) (F : GA D (Wc D j) → ℂ)
    (x : GA D (Wc D j)) : ρ.hecke i j b k P R z F x = (((ρ.B i j b).mu z : Circle) : ℂ)⁻¹ *
      (((normV P : ℕ) : ℂ) ^ (k * ((Vc D j).rank / 2)))⁻¹ * ∑ γ ∈ R, F (x * γ) := by
  simp only [hecke, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.funLeft_apply]

end Setup

section Hecke

variable {ρ : Setup X} {Y : NExp D.R D.host D.what₂ D.LL0 N X} {i : X.Tw} {j : Fin D.R.m} {b : Bool} (rd : Rd ρ Y i j b)

def HeckeAt (k : ℕ) (P : Pl D.host.E) (f g : Y.Fm i ((j : ℕ) + 1) b) : Prop :=
  ∀ α R z, ρ.IsHeckeDatum i j b k P α R z → rd g = ρ.hecke i j b k P R z (rd f)

def HeckeTie : Prop :=
  ∀ k P, HkIdx i k P → ∀ f, (∃ g, HeckeAt rd k P f g) → HeckeAt rd k P f (Y.hkF i _ b k P f)

def RatHecke : Prop := ∀ k P, HkIdx i k P → ∀ f, ∃ g, HeckeAt rd k P f g

variable {rd}

theorem heckeRead_iff : HeckeRead rd ↔ ∀ k P, HkIdx i k P → ∀ f, HeckeAt rd k P f (Y.hkF i _ b k P f) :=
  ⟨fun h k P hk f α R z d => funext fun x => (h k P hk α R z d.1 d.2 d.3 f x).trans (ρ.hecke_apply ..).symm,
    fun h k P hk α R z h1 h2 h3 f x => (congrFun (h k P hk f α R z ⟨h1, h2, h3⟩) x).trans (ρ.hecke_apply ..)⟩

theorem heckeRead_iff_tie : HeckeRead rd ↔ HeckeTie rd ∧ RatHecke rd := by
  rw [heckeRead_iff]
  exact ⟨fun h => ⟨fun k P hk f _ => h k P hk f, fun k P hk f => ⟨_, h k P hk f⟩⟩,
    fun h k P hk f => h.1 k P hk f (h.2 k P hk f)⟩

theorem HeckeTie.heckeRead (h : HeckeTie rd) (hR : RatHecke rd) : HeckeRead rd := heckeRead_iff_tie.2 ⟨h, hR⟩

theorem HeckeTie.eq (h : HeckeTie rd) (hinj : Function.Injective rd) {k P} (hk : HkIdx i k P) {α R z}
    (d : ρ.IsHeckeDatum i j b k P α R z) {f g : Y.Fm i ((j : ℕ) + 1) b} (hg : HeckeAt rd k P f g) : Y.hkF i _ b k P f = g :=
  hinj ((h k P hk f ⟨g, hg⟩ α R z d).trans (hg α R z d).symm)


theorem exists_hecke (hinj : Function.Injective rd) (k : ℕ) (P : Pl D.host.E) :
    ∃ T : Module.End (FractionRing (X.O i)) (Y.Fm i ((j : ℕ) + 1) b), ∀ f, (∃ g, HeckeAt rd k P f g) → HeckeAt rd k P f (T f) := by
  obtain ⟨T, hT⟩ := exists_end_reads rd hinj
    fun a : {a : GA D (Wc D j) × Finset (GA D (Wc D j)) × (AE D)ˣ // ρ.IsHeckeDatum i j b k P a.1 a.2.1 a.2.2} =>
      ρ.hecke i j b k P a.1.2.1 a.1.2.2
  exact ⟨T, fun f ⟨g, hg⟩ α R z d => hT f ⟨g, fun a => hg _ _ _ a.2⟩ ⟨(α, R, z), d⟩⟩

theorem CellTie.injective_rdK {hρ : ρ.Good} (T : CellTie hρ Y rd) (k : ℕ) : Function.Injective (rdK rd hρ k) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨d⟩ := T.nonempty_dat
  have h := (T.thPsi_iff k ∅ 1 (twOK_one i k) d ((1 : X.Ok i k) ⊗ₜ[X.O i] Y.th i _ b d + x)).2 (by
    rw [map_add, hx, add_zero, rdK_tmul, map_one, one_smul, T.th_eq, Setup.gens_one]
    rfl)
  rw [Y.thPsi_one] at h
  exact add_eq_left.1 h

end Hecke

section Univ


theorem InRange.twSet {i : X.Tw} {Q : Finset (Pl D.host.E)} (h : InRange X i Q) : TWSet X i Q :=
  fun v hv => ⟨h.1 v hv, fun hl => Finset.disjoint_left.1 h.2.2 hv (X.twistExcludedPlaces_contains_residueChar i hl)⟩

theorem twSet_of_twOK {i : X.Tw} {k : ℕ} {Q : Finset (Pl D.host.E)} {ψ} (h : TwOK (X := X) i k Q ψ) : TWSet X i Q :=
  fun v hv => ⟨h.1 v hv, fun hl => Finset.disjoint_left.1 h.2.1 hv (X.twistExcludedPlaces_contains_residueChar i hl)⟩

variable {Y : NExp D.R D.host D.what₂ D.LL0 N X} (hY : IsUnivChar Y) {i : X.Tw} {Q : Finset (Pl D.host.E)} {M : ℕ}
include hY

theorem delU_off (hQ : TWSet X i Q) (σ : G D.host.E N.Om) (v : ↥Q) (hv : v.1 ∉ admissibleConjugatePairPlaces X i Q M) :
    Multiplicative.toAdd (Y.delU i Q M σ) v = 0 := by
  classical
  rw [hY, GalChar.delU_apply, GalChar.delCoord]
  split_ifs with h
  · rw [GalChar.delOf, dif_neg]
    · rfl
    rintro ⟨d, h1, h2, h3, h4, h5⟩
    obtain ⟨P', hc⟩ := GlobalTheory.TwistDet.exists_isConjPl v.1
    have hP' : P' ∈ Q := h (Or.inr hc)
    have key : ∀ P, GalChar.pair D.host P = GalChar.pair D.host v.1 →
        ∃ χ : G D.host.E N.Om →* Multiplicative (ZMod (X.l i ^ M)), IsOpen (χ.ker : Set (G D.host.E N.Om)) ∧ AntiHom X.cc χ ∧
        (∀ w ∈ placesOver D.host.E (X.l i), ∀ A : ValuationSubring N.Om, IsPlaceOver A w →
          ∀ σ ∈ Dec (F := D.host.E) A, χ σ = 1) ∧
        (∀ w : PlE D.host, w ≠ P → ¬ IsConjPl D.host P w → ∀ A : ValuationSubring N.Om, IsPlaceOver A w →
          ∀ σ ∈ Ine (F := D.host.E) A, χ σ = 1) ∧
        ∀ A : ValuationSubring N.Om, IsPlaceOver A P →
          Function.Surjective fun σ : Ine (F := D.host.E) A => Multiplicative.toAdd (χ σ) := fun P e =>
      ⟨d, h1, h2, h3, fun w a c => h4 w (e ▸ fun t => t.elim a c), fun A hA x => by
        obtain ⟨σ, hσ, hx⟩ := h5 P (e ▸ Or.inl rfl) A hA (Multiplicative.ofAdd x)
        exact ⟨⟨σ, hσ⟩, congrArg Multiplicative.toAdd hx⟩⟩
    refine hv (mem_admissibleConjugatePairPlaces_iff.2 ⟨v.2, P', hP', hc, fun w hw => ?_, fun w hw => ?_⟩)
    · rcases Finset.mem_insert.1 hw with rfl | hw
      · exact hQ _ v.2
      · exact Finset.mem_singleton.1 hw ▸ hQ _ hP'
    · rcases Finset.mem_insert.1 hw with rfl | hw
      · exact ⟨⟨P', by simp, hc⟩, key _ rfl⟩
      · obtain rfl := Finset.mem_singleton.1 hw
        exact ⟨⟨v.1, by simp, GalChar.isConjPl_symm hc⟩, key _ (GalChar.pair_eq hc)⟩
  · rfl

theorem delU_on (σ : G D.host.E N.Om) (v : ↥Q) (hv : v.1 ∈ admissibleConjugatePairPlaces X i Q M) :
    Multiplicative.toAdd (Y.delU i Q M σ) v =
      Multiplicative.toAdd (GalChar.delOf D.host X.cc (X.l i) M (GalChar.pair D.host v.1) σ) := by
  rw [hY, GalChar.delU_apply, GalChar.delCoord, if_pos]
  rintro w (rfl | hw)
  · exact v.2
  · exact admissibleConjugatePairPlaces_subset i Q M (conj_mem_admissibleConjugatePairPlaces hv hw)

theorem delU_eq_coord (hQ : TWSet X i Q) (σ : G D.host.E N.Om) (v : ↥Q) :
    Multiplicative.toAdd (Y.delU i Q M σ) v = Multiplicative.toAdd (coord Y i (admissibleConjugatePairPlaces X i Q M) M v.1 σ) := by
  by_cases hv : v.1 ∈ admissibleConjugatePairPlaces X i Q M
  · rw [delU_on hY σ v hv, coord_apply _ _ _ _ hv, hY, GalChar.delU_apply,
      GalChar.delCoord_of_closed _ _ _ (fun _ h _ hc => conj_mem_admissibleConjugatePairPlaces h hc) M hv]
  · rw [delU_off hY hQ σ v hv, coord, dif_neg hv]
    rfl

theorem delU_eq_spread (hQ : TWSet X i Q) {ch : Set (Pl D.host.E)} (hch : IsChoice ch) (σ : G D.host.E N.Om) :
    Multiplicative.toAdd (Y.delU i Q M σ) =
      spread Y i Q M ch fun P => Multiplicative.toAdd (coord Y i (admissibleConjugatePairPlaces X i Q M) M P.1 σ) :=
  funext fun v => (delU_eq_coord hY hQ σ v).trans (spread_coord Y i Q M hch σ v).symm


end Univ

section Full

variable {ρ : Setup X} (hρ : ρ.Good) {Y : NExp D.R D.host D.what₂ D.LL0 N X} (rd : Rds Y ρ)

structure FullTie : Type where

  tie : Comparison₂ hρ rd

  hecke : ∀ i j b, HeckeTie (rd i j b)

  univ : IsUnivChar Y

variable (hF : ∀ i j b, Faithful (rd i j b))

open Classical in

def Model.hkF (i : X.Tw) : ∀ n b, ℕ → Pl D.host.E → Module.End (FractionRing (X.O i)) (Y.Fm i n b)
  | 0, b => Y.hkF i 0 b
  | n + 1, b => fun k P =>
    if h : n < D.R.m ∧ HkIdx i k P then (exists_hecke (hF i ⟨n, h.1⟩ b).injective k P).choose else Y.hkF i (n + 1) b k P

def withHecke : NExp D.R D.host D.what₂ D.LL0 N X := { Y with hkF := Model.hkF rd hF }

theorem heckeTie_withHecke (i j b) : HeckeTie (Y := withHecke rd hF) (rd i j b) := fun k P hk f hf => by
  have e : Model.hkF rd hF i ((j : ℕ) + 1) b k P = (exists_hecke (hF i j b).injective k P).choose := dif_pos ⟨j.2, hk⟩
  have h := (exists_hecke (hF i j b).injective k P).choose_spec f hf
  rw [← e] at h
  exact h


variable (hL : ρ.LatFG)

def withAll : NExp D.R D.host D.what₂ D.LL0 N X :=
  withSeries hρ (Y := withHecke (Y := withUnivChar Y) rd hF) rd hF hL

def fullTieWithAll (hU : ρ.LevelOf Y) : FullTie hρ (Y := withAll hρ rd hF hL) rd where
  tie := tieWithSeries hρ (Y := withHecke (Y := withUnivChar Y) rd hF) rd hF hL ⟨hU.1, hU.2⟩
  hecke := heckeTie_withHecke (Y := withUnivChar Y) rd hF
  univ := fun _ _ _ => rfl

end Full

example (ρ : Setup X) (i j b) (P : Pl D.host.E) (F : GA D (Wc D j) → ℂ) : ρ.hecke i j b 0 P {1} 1 F = F := by
  funext x
  simp [Setup.hecke_apply]

end GlobalTheory.SeriesTie

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
open Formalism.L2.Host (embLL0)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd)

structure RealPin (ρ : Setup D.ntw) : Prop where
  psi : ∀ i j b, (ρ.B i j b).F.ψ = Rl.ψ
  inf : ∀ i j b, (ρ.B i j b).F.θ = Rl.θ
  cartT : ∀ i j b, (ρ.B i j b).F.sT = cart (Rl.MW j (sg0 D A3.A))
  onbS : ∀ i j b τ, ((ρ.B i j b).F.BS τ).val = Rl.BV j τ
  onbT : ∀ i j b, (ρ.B i j b).F.BT = onb (Rl.MW j (sg0 D A3.A))
  latS : ∀ i j b, (ρ.B i j b).F.ΛS = Rl.ΛV j
  latT : ∀ i j b, (ρ.B i j b).F.ΛT = Rl.ΛW j
  frS : ∀ i j b, (ρ.B i j b).F.βS = Rl.βV j
  frT : ∀ i j b, (ρ.B i j b).F.βT = Rl.βW j
  vac : ∀ i j b, (ρ.B i j b).F.f₀ = Rl.vacP j
  Pg : ∀ i j b, (ρ.B i j b).G.Pg = Rl.Pg
  grp : ∀ i j b (g : G0g D.nd) (P : Pl D.host.E) (h : P ∈ (ρ.B i j b).G.Pg) (h' : P ∈ Rl.Pg) (a c : Fin (Wc D j).rank),
    (ρ.eG i j b g ⟨P, h⟩).val a c = (cG.symm g ⟨P, h'⟩).val (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c)
  mu0 : ∀ i j b, (ρ.B i j b).mu0 = Rl.mu0 ((j : ℕ) + 1)
  eta : ∀ i j b, (ρ.B i j b).eta = Rl.eta
  delta : ∀ i j b, ChrEq (ρ.B i j b).de.chi (Rl.C.delAt (D.ntw.l i))
  deltaPl : ∀ i t, ∀ P ∈ Rl.Q t, P ∈ D.ntw.pD i → P ∈ ρ.ch i
  ap : ∀ i j b τ, (ρ.B i j b).w.ap τ = aPl D j ((Wc D j).sig (tauE D τ)).1 τ
  am : ∀ i j b τ, (ρ.B i j b).w.am τ = aMi D j ((Wc D j).sig (tauE D τ)).1 ((Wc D j).sig (tauE D τ)).2 τ

variable {Rl cG} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)

def evW (j : Fin D.R.m) : S.WL ((j : ℕ) + 1) →+ (GA D (Wc D j) → ℂ) where
  toFun x := (Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e x)) (v₀ j _)
  map_zero' := by rw [map_zero, map_zero, map_zero]; rfl
  map_add' x y := by rw [map_add, map_add, map_add]; rfl

theorem evW_smul (j : Fin D.R.m) (c : D.what₂.LL) (x : S.WL ((j : ℕ) + 1)) :
    evW YS v₀ j (c • x) = D.what₂.embLL c • evW YS v₀ j x := by
  change (Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e (c • x))) (v₀ j _) = _
  rw [map_smul, map_smulₛₗ, map_smul, show sg0 D A3.A c = D.what₂.embLL c from
    congrArg (fun f : D.what₂.LL →+* ℂ => f c) (sgAt_mk _ Rl.hv0)]
  rfl

section Read

variable {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

def evK : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1) →+ (GA D (Wc D j) → ℂ) :=
  TensorProduct.liftAddHom
    { toFun := fun a => (DistribSMul.toAddMonoidHom _ (ρ.e i b a)).comp
        ((evW YS v₀ j).comp (S.A ((j : ℕ) + 1)).WK.subtype.toAddMonoidHom)
      map_zero' := by ext; simp [show ρ.e i b (0 : NX.KB S i b) = 0 from map_zero _]
      map_add' := fun x y => by ext; simp [show ρ.e i b (x + y : NX.KB S i b) = ρ.e i b x + ρ.e i b y from map_add _ _ _, add_mul] }
    fun c a f => by
      change ρ.e i b (sideEmb D.ntw i b (S.kKs c) * (show FractionRing (D.ntw.O i) from a)) • evW YS v₀ j (Subtype.val f) =
        ρ.e i b a • evW YS v₀ j (c • Subtype.val f)
      rw [← algebraMap_smul D.what₂.LL c, evW_smul, map_mul, hρ.e_LL0, smul_smul, mul_comm, ← S.kKs_spec]
      rfl

theorem evK_tmul (a : NX.KB S i b) (f : NX.FmK S ((j : ℕ) + 1)) :
    evK YS v₀ hρ i j b (a ⊗ₜ f) = ρ.e i b a • evW YS v₀ j (Subtype.val f) := rfl

def realRd (ν : ℂ) : Rd ρ D.nexp i j b where
  toFun f := ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)
  map_add' f f' := by
    rw [map_add, ← smul_add]
    exact congrArg _ ((evK YS v₀ hρ i j b).map_add _ _)
  map_smul' c f := by
    rw [map_smul, smul_comm]
    congr 1
    generalize YS.eF i _ b (Nat.le_add_left _ _) j.2 f = x
    have key : ∀ (c : NX.KB S i b) (x : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)),
        evK YS v₀ hρ i j b (c • x) = ρ.e i b c • evK YS v₀ hρ i j b x := fun c x => by
      induction x using TensorProduct.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
      | tmul a f =>
        rw [TensorProduct.smul_tmul', evK_tmul, evK_tmul, smul_smul]
        exact congrArg (· • _) (map_mul (ρ.e i b) c a)
    exact key c x

theorem realRd_tmul (ν : ℂ) (a : NX.KB S i b) (f : NX.FmK S ((j : ℕ) + 1)) :
    realRd YS v₀ hρ i j b ν ((YS.eF i _ b (Nat.le_add_left _ _) j.2).symm (a ⊗ₜ[S.Ks] f : NX.KB S i b ⊗[S.Ks] _)) =
      (ν⁻¹ * ρ.e i b a) • evW YS v₀ j (Subtype.val f) := by
  change ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b _ j.2 ((YS.eF i _ b _ j.2).symm _)) = _
  rw [mul_smul]
  exact congrArg (fun x => ν⁻¹ • evK YS v₀ hρ i j b x) ((YS.eF i _ b (Nat.le_add_left _ _) j.2).apply_symm_apply _)

theorem realRd_apply (ν : ℂ) (f : D.nexp.Fm i ((j : ℕ) + 1) b) :
    realRd YS v₀ hρ i j b ν f = ν⁻¹ • realRd YS v₀ hρ i j b 1 f := by
  change _ = ν⁻¹ • (1 : ℂ)⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)
  rw [inv_one, one_smul]
  rfl

end Read

variable (Rl) in

def IsScale {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) (c : ℂ) : Prop :=
  ∃ gramR c0R c0L, Bridge.FamTie Rl.B Rl.pl (Rl.Sb : Set (Pl D.host.E)) Rl.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
      (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L ∧
    ∃ u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ, (∀ τ, (u τ : (Rl.MW j (sg0 D A3.A)).sm τ) = v₀ j _ τ) ∧
      ∀ F : VV D.what₂.LL (FWT.lamV D j),
        harmFn (Wc D j).rank B.w B.F.BS (Rl.ioP j (PiTensorProduct.tprod ℂ u) (c0L j F)) =
          c • coefFn D.what₂.embLL (FWT.lamV D j) (F : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank)

variable (Rl) in

def IsNorm {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) (ν : ℂ) : Prop :=
  ν ≠ 0 ∧ ∃ c, IsScale Rl v₀ B c ∧ ∃ n : ℕ, n ≠ 0 ∧ ν ^ n = (cj (twAt D.what₂.embLL A3.A.v0) (Rl.phs j) * c) ^ n

theorem heckeAt_realRd {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) {ν : ℂ} (hν : ν ≠ 0) (k P f g) :
    HeckeAt (realRd YS v₀ hρ i j b ν) k P f g ↔ HeckeAt (realRd YS v₀ hρ i j b 1) k P f g := by
  refine forall₃_congr fun α R z => imp_congr_right fun _ => ?_
  rw [realRd_apply YS v₀ hρ i j b ν, realRd_apply YS v₀ hρ i j b ν f, map_smul]
  exact (smul_right_injective _ (inv_ne_zero hν)).eq_iff

def RatRow {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) : Prop :=
  ∃ ν, IsNorm Rl v₀ (ρ.B i j b) ν ∧ Rat hρ (realRd YS v₀ hρ i j b ν)

structure IsScalar {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ) : Prop where
  ne : ν ≠ 0
  norm : (∃ ν', IsNorm Rl v₀ (ρ.B i j b) ν') → IsNorm Rl v₀ (ρ.B i j b) ν
  rat : RatRow YS v₀ hρ i j b → Rat hρ (realRd YS v₀ hρ i j b ν)

theorem exists_isScalar {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) :
    ∃ ν, IsScalar YS v₀ hρ i j b ν := by
  by_cases h : RatRow YS v₀ hρ i j b
  · obtain ⟨ν, h1, h2⟩ := h
    exact ⟨ν, h1.1, fun _ => h1, fun _ => h2⟩
  · by_cases h' : ∃ ν', IsNorm Rl v₀ (ρ.B i j b) ν'
    · obtain ⟨ν, h1⟩ := h'
      exact ⟨ν, h1.1, fun _ => h1, fun h2 => absurd h2 h⟩
    · exact ⟨1, one_ne_zero, fun h1 => absurd h1 h', fun h2 => absurd h2 h⟩

structure ExportTie : Type 1 where

  ρ : Setup D.ntw
  good : ρ.Good
  pin : RealPin Rl cG ρ

  vec : ∀ j, FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _)

  ν : D.ntw.Tw → Fin D.R.m → Bool → ℂ
  scalar : ∀ i j b, IsScalar YS v₀ good i j b (ν i j b)

  tie : Comparison₂ good (Y := D.nexp) fun i j b => realRd YS v₀ good i j b (ν i j b)

  hecke : ∀ i j b, HeckeTie (realRd YS v₀ good i j b (ν i j b))

  univ : GlobalTheory.UnivChar.IsUnivChar D.nexp

namespace ExportTie

variable {YS v₀} (Z : ExportTie YS v₀)

abbrev rd : Rds D.nexp Z.ρ := fun i j b => realRd YS v₀ Z.good i j b (Z.ν i j b)

def full : FullTie Z.good Z.rd := ⟨Z.tie, Z.hecke, Z.univ⟩

theorem heckeRead {i j b} (h : RatHecke (Z.rd i j b)) : HeckeRead (Z.rd i j b) := (Z.hecke i j b).heckeRead h

include Z in

theorem delU_ine (i : D.ntw.Tw) (Q : Finset (Pl D.host.E)) (M : ℕ) (hQ : Formalism.MainNotions.NAdm.AdmQ D.ntw i Q M) (P : Pl D.host.E)
    (hP : P ∈ Q) : (∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P →
      Function.Surjective fun σ : Ine (F := D.host.E) A => Multiplicative.toAdd (D.nexp.delU i Q M σ) ⟨P, hP⟩) ∧
    ∀ P' ∈ Q, P' ≠ P → ¬ IsConjPl D.host P P' → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A P' →
      ∀ σ ∈ Ine (F := D.host.E) A, Multiplicative.toAdd (D.nexp.delU i Q M σ) ⟨P, hP⟩ = 0 :=
  GlobalTheory.UnivCharIne.delU_ine D Z.univ i Q M hQ P hP

include Z in

theorem delUTie (hK : GlobalTheory.TwSys.K1 D.ntw) : GlobalTheory.TwSys.DelUTie D.nexp := GlobalTheory.UnivChar.delUTie_of_isUnivChar _ hK Z.univ

theorem rat {i j b} (h : RatRow YS v₀ Z.good i j b) : Rat Z.good (Z.rd i j b) := (Z.scalar i j b).rat h

include Z in

theorem thU_empty (i : D.ntw.Tw) (j : ℕ) (b : Bool) (M : ℕ) (d : D.nexp.Dat i j b) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    D.nexp.thU i j b ∅ M d = D.nexp.th i j b d ⊗ₜ[D.ntw.O i] 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' h1
  exact (Z.tie i ⟨n, h2⟩ b).thU_empty M d

theorem exists_dat {i j b} (h : RatRow YS v₀ Z.good i j b) {s g P} (hd : Z.ρ.IsDatum i j b s g P) :
    ∃ d, (Z.tie i j b).cls d = g ∧ (Z.tie i j b).coef d = P ∧ Z.rd i j b (D.nexp.th i _ b d) = Z.ρ.theta i j b g P := by
  obtain ⟨d, -, rfl, rfl⟩ := (Z.tie i j b).dat_onto s g P hd ((Z.rat h).1 s g P hd)
  exact ⟨d, rfl, rfl, (Z.tie i j b).th_eq d⟩

end ExportTie

example (i : D.ntw.Tw) (b : Bool) : NX.readLL0 S i b = sideEmb D.ntw i b := rfl

example (i : D.ntw.Tw) : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt false (D.ntw.delta i) = (D.ntw.delta i)⁻¹ := rfl

example : normProd (∅ : Finset (Pl D.host.E)) = 1 := rfl

end GlobalTheory.SeriesTie

end
end
