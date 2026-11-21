import Formalism.SharpRestriction.LevelLetterCocycles.KillWinFromCut
import Formalism.SharpRestriction.LevelLetterCocycles.MapEvalPsPi
import Formalism.SharpRestriction.LevelLetterCocycles.LocalInputsFromLiterature

section
namespace Formalism.MainNotions.UnusedSlot80.InvCut

open Formalism.MainNotions.N.Ln03

def PrecompConst : Prop :=
  ∀ (LL : Type) [Field LL] (l : ℕ) [Fact l.Prime] (s : ℕ) (S : Set (ZMod (l ^ (s + 1)))ˣ),
    Subgroup.closure S = ⊤ → ∀ f : Rs LL l s → LL, (∀ a ∈ S, precomp LL l s a f = f) →
      ∃ c : LL, ∀ ζ : Rs LL l s, f ζ = c

def GenUnits : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (s : ℕ) (u : ℤ_[l]ˣ),
    ((u : ℤ_[l]) - 1 ∈ Ideal.span {(l : ℤ_[l])}) → ((u : ℤ_[l]) - 1 ∉ Ideal.span {(l : ℤ_[l]) ^ 2}) →
      Subgroup.closure (insert (redU l s u) (Set.range fun d : DeltaT l => redU l s d.1)) = ⊤

end Formalism.MainNotions.UnusedSlot80.InvCut
end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.InvW

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

structure LevEv (W : LocWach PD LL O v n) (a : ZMod n) (s : ℕ) where
  F : Type
  fF : Field F
  algOF : Algebra O F
  hp : ((PD.p : ℕ) : F) ≠ 0
  ev : Rs F PD.p s → LetA O n →+* F
  ev_O : ∀ ζ (x : O), ev ζ (algebraMap O (LetA O n) x) = algebraMap O F x
  ev_letE : ∀ ζ, ev ζ (letE a) = 1
  ev_ps : ∀ ζ, ev ζ (ps W s) = 0
  ev_pt : ∀ t, t ≠ s → ∀ ζ, ev ζ (ps W t) ≠ 0
  σ : W.Gam → (ZMod (PD.p ^ (s + 1)))ˣ
  ev_γ : ∀ g ζ x, ev ζ (W.γA g x) = ev (powR F PD.p s (σ g) ζ) x
  gen : Subgroup.closure (insert (σ W.gam) (σ '' (W.DelF : Set W.Gam))) = ⊤
  div : ∀ g ∈ W.AΔ, (∀ ζ, ev ζ g = 0) → ∃ (κ : ℕ) (w : LetA O n), w ∈ W.AΔ ∧
    ((PD.p : ℕ) : LetA O n) ^ κ * (letE a * g) = ps W s * w
  rat : ∀ g ∈ W.AΔ, ∀ d ∈ W.AΔ, (∀ ζ, ev ζ d ≠ 0) → ∀ c : F, (∀ ζ, ev ζ g = c * ev ζ d) →
    ∃ (κ : ℕ) (x : O), ((PD.p : ℕ) : F) ^ κ * c = algebraMap O F x

attribute [instance] LevEv.fF LevEv.algOF

theorem invLevCore_of (W : LocWach PD LL O v n) (hπ : W.π₀ ∈ W.AΔ) (hL : ∀ a s, LevEv W a s)
    (hPC : InvCut.PrecompConst) : CutU.InvLevCore W := by
  intro _hA _hp a s T e hsT f hf hγ
  obtain ⟨u, hu, hfu⟩ := hf
  obtain ⟨κ, v, hv, hfv⟩ := hγ
  let L := hL a s
  letI : Field L.F := L.fF
  letI : Algebra O L.F := L.algOF
  set D : LetA O n := ∏ t ∈ T, ps W t ^ e t with hDdef
  set U : LetA O n := letE a * 1 * u with hUdef
  have hDΔ : D ∈ W.AΔ := Subalgebra.prod_mem _ fun t _ => Subalgebra.pow_mem _ (RatW.ps_mem W hπ t) _
  have hUΔ : U ∈ W.AΔ := W.AΔ.mul_mem (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W a) (W.AΔ.one_mem)) hu
  have hUe : letE a * U = U := by rw [hUdef, ← mul_assoc, ← mul_assoc, RatW.letE_idem]

  have hp0 : ((PD.p : ℕ) : L.F) ≠ 0 := L.hp
  have hγE' : algebraMap (LetA O n) W.EE (W.γA W.gam D) * W.γE W.gam f =
      algebraMap (LetA O n) W.EE (W.γA W.gam U) := by
    have h1 : W.γE W.gam (algebraMap (LetA O n) W.EE D * f) = W.γE W.gam (algebraMap (LetA O n) W.EE U) := by
      rw [hfu]
    rw [map_mul, W.γE_ext, W.γE_ext] at h1
    exact h1
  have hA : ((PD.p : ℕ) : LetA O n) ^ κ * (D * W.γA W.gam U - W.γA W.gam D * U) =
      W.γA W.gam D * (letE a * ps W s * v) := by
    apply W.EE_inj
    simp only [lE] at hfv
    simp only [map_mul, map_sub, map_pow, map_natCast] at hfv ⊢
    linear_combination (-(((PD.p : ℕ) : W.EE) ^ κ * algebraMap (LetA O n) W.EE D)) * hγE' +
      (((PD.p : ℕ) : W.EE) ^ κ * algebraMap (LetA O n) W.EE (W.γA W.gam D)) * hfu +
      algebraMap (LetA O n) W.EE (W.γA W.gam D) * hfv
  have hevD : ∀ ζ, L.ev ζ D ≠ 0 := fun ζ => by
    rw [hDdef, map_prod]
    exact Finset.prod_ne_zero_iff.2 fun t ht => by
      rw [map_pow]; exact pow_ne_zero _ (L.ev_pt t (fun h => hsT (h ▸ ht)) ζ)
  have hevA : ∀ ζ, L.ev ζ D * L.ev ζ (W.γA W.gam U) = L.ev ζ (W.γA W.gam D) * L.ev ζ U := fun ζ => by
    have h1 := congrArg (L.ev ζ) hA
    simp only [map_mul, map_sub, map_pow, map_natCast, L.ev_ps, mul_zero, zero_mul] at h1
    exact sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ hp0))
  let h : Rs L.F PD.p s → L.F := fun ζ => L.ev ζ U / L.ev ζ D
  have hinvΔ : ∀ δ ∈ W.DelF, ∀ ζ, h (powR L.F PD.p s (L.σ δ) ζ) = h ζ := fun δ hδ ζ => by
    simp only [h]
    rw [← L.ev_γ, ← L.ev_γ, hUΔ δ hδ, hDΔ δ hδ]
  have hinvγ : ∀ ζ, h (powR L.F PD.p s (L.σ W.gam) ζ) = h ζ := fun ζ => by
    simp only [h]
    rw [← L.ev_γ, ← L.ev_γ]
    have hγD : L.ev ζ (W.γA W.gam D) ≠ 0 := by rw [L.ev_γ]; exact hevD _
    rw [div_eq_div_iff hγD (hevD ζ)]
    linear_combination hevA ζ
  obtain ⟨c, hc⟩ := hPC L.F PD.p s _ L.gen h (by
    rintro x (rfl | ⟨δ, hδ, rfl⟩)
    · funext ζ; rw [precomp_apply]; exact hinvγ ζ
    · funext ζ; rw [precomp_apply]; exact hinvΔ δ hδ ζ)
  have hUc : ∀ ζ, L.ev ζ U = c * L.ev ζ D := fun ζ => by
    have := hc ζ
    simp only [h] at this
    rw [div_eq_iff (hevD ζ)] at this
    exact this
  obtain ⟨κ1, x, hx⟩ := L.rat U hUΔ D hDΔ hevD c hUc
  set g : LetA O n := ((PD.p : ℕ) : LetA O n) ^ κ1 * U - algebraMap O (LetA O n) x * D with hgdef
  have hgΔ : g ∈ W.AΔ := W.AΔ.sub_mem (W.AΔ.mul_mem (W.AΔ.pow_mem (W.AΔ.natCast_mem _) _) hUΔ)
    (W.AΔ.mul_mem (W.AΔ.algebraMap_mem x) hDΔ)
  have hg0 : ∀ ζ, L.ev ζ g = 0 := fun ζ => by
    rw [hgdef, map_sub, map_mul (L.ev ζ) (((PD.p : ℕ) : LetA O n) ^ κ1) U,
      map_mul (L.ev ζ) (algebraMap O (LetA O n) x) D, map_pow, map_natCast, L.ev_O, hUc ζ, ← hx]
    ring
  obtain ⟨κ2, w, hw, hgw⟩ := L.div g hgΔ hg0
  refine ⟨κ1 + κ2, ((PD.p : ℕ) : O) ^ κ2 * x, w, hw, ?_⟩
  have hlw : letE a * ps W s * w = ps W s * w := by
    calc letE a * ps W s * w = letE a * (ps W s * w) := mul_assoc _ _ _
      _ = letE a * (((PD.p : ℕ) : LetA O n) ^ κ2 * (letE a * g)) := by rw [hgw]
      _ = ((PD.p : ℕ) : LetA O n) ^ κ2 * ((letE a * letE a) * g) := by ring
      _ = ps W s * w := by rw [RatW.letE_idem, hgw]
  rw [hlw, ← hgw]
  have hO : algebraMap O W.EE (((PD.p : ℕ) : O) ^ κ2 * x) =
      algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) (((PD.p : ℕ) : O) ^ κ2 * x)) :=
    IsScalarTower.algebraMap_apply O (LetA O n) W.EE _
  rw [hO]
  simp only [lE, hgdef]
  have hUe' : letE a * (((PD.p : ℕ) : LetA O n) ^ κ1 * U - algebraMap O (LetA O n) x * D) =
      ((PD.p : ℕ) : LetA O n) ^ κ1 * U - letE a * algebraMap O (LetA O n) x * D := by
    rw [mul_sub, mul_left_comm, hUe, mul_assoc]
  rw [hUe']
  simp only [map_mul, map_sub, map_pow, map_natCast] at hfu ⊢
  linear_combination (((PD.p : ℕ) : W.EE) ^ (κ1 + κ2)) * hfu

end Core

end Formalism.MainNotions.UnusedSlot80.InvW
end
end

section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80.InvW

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03

section Parts

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

structure LevBasics (W : LocWach PD LL O v n) (a : ZMod n) (s : ℕ) where
  F : Type
  fF : Field F
  algOF : Algebra O F
  inj : Function.Injective (algebraMap O F)
  hp : ((PD.p : ℕ) : F) ≠ 0
  root : ∃ ζ : F, IsPrimitiveRoot ζ (PD.p ^ (s + 1))
  ev : Rs F PD.p s → LetA O n →+* F
  ev_O : ∀ (ζ : Rs F PD.p s) (x : O), ev ζ (algebraMap O (LetA O n) x) = algebraMap O F x
  ev_letE : ∀ ζ : Rs F PD.p s, ev ζ (letE a) = 1
  ev_π : ∀ ζ : Rs F PD.p s, ev ζ letπ = (ζ : F) - 1
  ev_ps : ∀ ζ : Rs F PD.p s, ev ζ (ps W s) = 0
  ev_pt : ∀ t, t ≠ s → ∀ ζ : Rs F PD.p s, ev ζ (ps W t) ≠ 0
  σ : W.Gam → (ZMod (PD.p ^ (s + 1)))ˣ
  ev_γ : ∀ g (ζ : Rs F PD.p s) x, ev ζ (W.γA g x) = ev (powR F PD.p s (σ g) ζ) x
  gen : Subgroup.closure (insert (σ W.gam) (σ '' (W.DelF : Set W.Gam))) = ⊤

attribute [instance] LevBasics.fF LevBasics.algOF

def LevDiv (W : LocWach PD LL O v n) (a : ZMod n) (s : ℕ) (F : Type) [Field F] [Algebra O F]
    (ev : Rs F PD.p s → LetA O n →+* F) : Prop :=
  ∀ g ∈ W.AΔ, (∀ ζ : Rs F PD.p s, ev ζ g = 0) → ∃ (κ : ℕ) (w : LetA O n), w ∈ W.AΔ ∧
    ((PD.p : ℕ) : LetA O n) ^ κ * (letE a * g) = ps W s * w

def LevRat (W : LocWach PD LL O v n) (a : ZMod n) (s : ℕ) (F : Type) [Field F] [Algebra O F]
    (ev : Rs F PD.p s → LetA O n →+* F) : Prop :=
  ∀ g ∈ W.AΔ, ∀ d ∈ W.AΔ, (∀ ζ : Rs F PD.p s, ev ζ d ≠ 0) → ∀ c : F,
    (∀ ζ : Rs F PD.p s, ev ζ g = c * ev ζ d) →
    ∃ (κ : ℕ) (x : O), ((PD.p : ℕ) : F) ^ κ * c = algebraMap O F x

def levEv_of (W : LocWach PD LL O v n) (a : ZMod n) (s : ℕ) (hB : LevBasics W a s) (hD : LevDiv W a s hB.F hB.ev)
    (hR : LevRat W a s hB.F hB.ev) : LevEv W a s where
  F := hB.F
  fF := hB.fF
  algOF := hB.algOF
  hp := hB.hp
  ev := hB.ev
  ev_O := hB.ev_O
  ev_letE := hB.ev_letE
  ev_ps := hB.ev_ps
  ev_pt := hB.ev_pt
  σ := hB.σ
  ev_γ := hB.ev_γ
  gen := hB.gen
  div := hD
  rat := hR

theorem invLevCore_of_parts (W : LocWach PD LL O v n) (hπ : W.π₀ ∈ W.AΔ) (hB : ∀ a s, LevBasics W a s)
    (hD : ∀ a s, LevDiv W a s (hB a s).F (hB a s).ev) (hR : ∀ a s, LevRat W a s (hB a s).F (hB a s).ev)
    (hPC : InvCut.PrecompConst) : CutU.InvLevCore W :=
  invLevCore_of W hπ (fun a s => levEv_of W a s (hB a s) (hD a s) (hR a s)) hPC

end Parts

end Formalism.MainNotions.UnusedSlot80.InvW
end
end

section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.InvW

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.N.Ln03 PowerSeries

section Div

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem isUnit_of_mk {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R] {x : R}
    (hx : IsUnit (Ideal.Quotient.mk I x)) : IsUnit x := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
  have h1 : x * y' - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hy, map_one, sub_self]
  have h2 := Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot I h1) 1
  rw [mul_one, sub_add_cancel] at h2
  exact isUnit_of_mul_isUnit_left h2

theorem aeval_X_coe {R : Type} [CommRing R] (r : Polynomial R) :
    Polynomial.aeval (PowerSeries.X : PowerSeries R) r = (r : PowerSeries R) := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, hp, hq, Polynomial.coe_add]
  | monomial k c =>
    rw [Polynomial.aeval_monomial, Polynomial.coe_monomial, PowerSeries.monomial_eq_mk]
    ext m
    simp [PowerSeries.coeff_X_pow, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, eq_comm]

theorem map_aeval {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x : PowerSeries R) (P : Polynomial R) :
    PowerSeries.map f (Polynomial.aeval x P) = Polynomial.aeval (PowerSeries.map f x) (P.map f) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.eval₂_map]
  congr 1
  ext c : 1
  simp [PowerSeries.algebraMap_eq]

variable [IsDomain O] [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]

theorem wdiv_ps (W : LocWach PD LL O v n) (hR : ToolsR.RingP W) (hT : Formalism.MainNotions.WachCoordinates.ToolsAlg W)
    (hpu : ¬ IsUnit ((PD.p : ℕ) : O)) (a : ZMod n) (s : ℕ) (f : PowerSeries O) :
    ∃ (H : PowerSeries O) (r : Polynomial O), r.degree < ((PD.p - 1) * PD.p ^ s : ℕ) ∧
      f = ps W s a * H + (r : PowerSeries O) := by
  set I : Ideal O := Ideal.span {((PD.p : ℕ) : O)} with hIdef
  have : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr (by
    rw [Ne, hIdef, Ideal.span_singleton_eq_top]; exact hpu)
  set N : ℕ := (PD.p - 1) * PD.p ^ s with hN
  set D : PowerSeries O := ps W s a with hDdef
  obtain ⟨u, P, hu, hPm, hPd, hPc, hps⟩ := hT.2.1 s
  obtain ⟨w, hw, hπw⟩ := ToolsR.π₀_comp hR
  have hD : D = u a * Polynomial.aeval W.π₀₁ P := by
    have h1 := congrFun hps a
    rw [Pi.mul_apply] at h1
    rw [hDdef, show ps W s = Formalism.MainNotions.WachCoordinates.pS W s from rfl, h1]
    congr 1
    exact (Polynomial.aeval_algHom_apply (Pi.evalAlgHom O (fun _ : ZMod n => PowerSeries O) a) W.π₀ P).symm
  have hPmap : P.map (Ideal.Quotient.mk I) = Polynomial.X ^ (PD.p ^ s) := by
    ext k
    rw [Polynomial.coeff_map, Polynomial.coeff_X_pow]
    rcases lt_trichotomy k (PD.p ^ s) with hk | rfl | hk
    · rw [if_neg hk.ne, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton.2 (hPc k hk)
    · rw [if_pos rfl, ← hPd, hPm.coeff_natDegree, map_one]
    · rw [if_neg hk.ne', Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
  set V : PowerSeries (O ⧸ I) := PowerSeries.map (Ideal.Quotient.mk I) (u a) *
    PowerSeries.map (Ideal.Quotient.mk I) w ^ (PD.p ^ s) with hV
  have hmapD : PowerSeries.map (Ideal.Quotient.mk I) D = V * PowerSeries.X ^ N := by
    rw [hD, map_mul, map_aeval, hPmap, Polynomial.aeval_X_pow, hπw, map_mul, map_pow, PowerSeries.map_X, hV, hN,
      mul_pow, ← pow_mul, mul_comm (PD.p - 1) (PD.p ^ s)]
    ring
  have huV : IsUnit (PowerSeries.constantCoeff V) := by
    rw [hV, map_mul, map_pow]
    refine IsUnit.mul ?_ (IsUnit.pow _ ?_)
    · have := ((hu.map (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) a)).map
        (PowerSeries.map (Ideal.Quotient.mk I))).map PowerSeries.constantCoeff
      simpa using this
    · exact (hw.map (PowerSeries.map (Ideal.Quotient.mk I))).map PowerSeries.constantCoeff
  have hcN : PowerSeries.coeff N (PowerSeries.map (Ideal.Quotient.mk I) D) = PowerSeries.constantCoeff V := by
    rw [hmapD, PowerSeries.coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff]
  have hord : (PowerSeries.map (Ideal.Quotient.mk I) D).order.toNat = N := by
    have : (PowerSeries.map (Ideal.Quotient.mk I) D).order = N := by
      refine PowerSeries.order_eq_nat.2 ⟨by rw [hcN]; exact huV.ne_zero, fun i hi => ?_⟩
      rw [hmapD, PowerSeries.coeff_mul_X_pow', if_neg (by omega)]
    rw [this, ENat.toNat_natCast]
  have hdiv : D.IsWeierstrassDivisorAt I := by
    unfold PowerSeries.IsWeierstrassDivisorAt
    rw [hord]
    refine isUnit_of_mk I ?_
    rw [← PowerSeries.coeff_map, hcN]
    exact huV
  have HD := hdiv.isWeierstrassDivisionAt_div_mod f
  refine ⟨hdiv.div f, hdiv.mod f, ?_, HD.eq_mul_add⟩
  have := HD.degree_lt
  rwa [hord] at this

theorem ev_aeval {W : LocWach PD LL O v n} {a : ZMod n} {s : ℕ} (hB : LevBasics W a s) (ζ : Rs hB.F PD.p s)
    (r : Polynomial O) : hB.ev ζ (Polynomial.aeval (letπ : LetA O n) r) = Polynomial.aeval ((ζ : hB.F) - 1) r := by
  let evA : LetA O n →ₐ[O] hB.F := { hB.ev ζ with commutes' := hB.ev_O ζ }
  rw [← hB.ev_π ζ]
  exact (Polynomial.aeval_algHom_apply evA letπ r).symm

theorem card_Rs {W : LocWach PD LL O v n} {a : ZMod n} {s : ℕ} (hB : LevBasics W a s) :
    Fintype.card (Rs hB.F PD.p s) = (PD.p - 1) * PD.p ^ s := by
  obtain ⟨ζ₀, hζ₀⟩ := hB.root
  rw [Fintype.card_coe, hζ₀.card_primitiveRoots, Nat.totient_prime_pow_succ PD.hp, mul_comm]

theorem poly_eq_zero {W : LocWach PD LL O v n} {a : ZMod n} {s : ℕ} (hB : LevBasics W a s) (r : Polynomial hB.F)
    (hdeg : r.natDegree < (PD.p - 1) * PD.p ^ s) (h : ∀ ζ : Rs hB.F PD.p s, Polynomial.eval ((ζ : hB.F) - 1) r = 0) :
    r = 0 :=
  Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (f := fun ζ : Rs hB.F PD.p s => (ζ : hB.F) - 1)
    (fun x y hxy => Subtype.ext (sub_left_injective hxy)) h (by rw [card_Rs hB]; exact hdeg)

theorem levDiv_of (W : LocWach PD LL O v n) (hR : ToolsR.RingP W) (hT : Formalism.MainNotions.WachCoordinates.ToolsAlg W)
    (hpu : ¬ IsUnit ((PD.p : ℕ) : O)) (a : ZMod n) (s : ℕ) (hB : LevBasics W a s) : LevDiv W a s hB.F hB.ev := by
  intro g hg hev
  have hNpos : 0 < (PD.p - 1) * PD.p ^ s := Nat.mul_pos (by have := PD.hp.two_le; omega) (pow_pos PD.hp.pos _)
  obtain ⟨H, r, hdeg, heq⟩ := wdiv_ps W hR hT hpu a s (g a)
  set wH : LetA O n := Pi.single a H with hwH
  have hRr : (fun _ : ZMod n => (r : PowerSeries O)) = Polynomial.aeval (letπ : LetA O n) r := by
    funext i
    show (r : PowerSeries O) = Pi.evalAlgHom O (fun _ : ZMod n => PowerSeries O) i (Polynomial.aeval letπ r)
    rw [← Polynomial.aeval_algHom_apply]
    exact (aeval_X_coe r).symm
  have key : (letE a : LetA O n) * g = ps W s * wH + letE a * Polynomial.aeval (letπ : LetA O n) r := by
    rw [← hRr]
    funext i
    by_cases hi : i = a
    · subst hi
      simp only [Pi.mul_apply, Pi.add_apply, hwH, letE, Pi.single_eq_same, one_mul, heq]
    · simp [Pi.mul_apply, Pi.add_apply, hwH, letE, Pi.single_eq_of_ne hi]
  have hroots : ∀ ζ : Rs hB.F PD.p s, Polynomial.eval ((ζ : hB.F) - 1) (r.map (algebraMap O hB.F)) = 0 := by
    intro ζ
    have h1 := congrArg (hB.ev ζ) key
    rw [map_mul, hB.ev_letE, one_mul, hev ζ, map_add, map_mul, hB.ev_ps, zero_mul, zero_add, map_mul,
      hB.ev_letE, one_mul, ev_aeval hB] at h1
    rw [Polynomial.eval_map, ← Polynomial.aeval_def]
    exact h1.symm
  have hr0 : r.map (algebraMap O hB.F) = 0 := by
    refine poly_eq_zero hB _ (lt_of_le_of_lt Polynomial.natDegree_map_le ?_) hroots
    by_cases hr : r = 0
    · rw [hr, Polynomial.natDegree_zero]; exact hNpos
    · exact (Polynomial.natDegree_lt_iff_degree_lt hr).2 hdeg
  have hr : r = 0 := Polynomial.map_injective _ hB.inj (by rw [hr0, Polynomial.map_zero])
  rw [hr, map_zero, mul_zero, add_zero] at key
  have hpsΔ : ps W s ∈ W.AΔ := RatW.ps_mem W hR.1 s
  have hp0 : ((PD.p : ℕ) : O) ≠ 0 := by
    intro h
    apply hB.hp
    rw [← map_natCast (algebraMap O hB.F), h, map_zero]
  have hps0 : ∀ i, ps W s i ≠ 0 := by
    intro i h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hT.2.2.1 s)
    have h1 := congrFun hc i
    have h2 := congrArg PowerSeries.constantCoeff h1
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.natCast_apply, map_mul, map_sub, map_natCast, LocWach.π₀,
      ToolsR.π₀₁_cc hR, mul_zero] at h2
    rw [show Formalism.MainNotions.WachCoordinates.pS W s i = ps W s i from rfl, h, map_zero, zero_sub, eq_comm, neg_eq_zero] at h2
    exact hp0 h2
  refine ⟨0, wH, ToolsR.cancel_AΔ hpsΔ hps0 ?_, by rw [pow_zero, one_mul, key]⟩
  rw [← key]
  exact W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W a) hg

end Div

end Formalism.MainNotions.UnusedSlot80.InvW
end
end
