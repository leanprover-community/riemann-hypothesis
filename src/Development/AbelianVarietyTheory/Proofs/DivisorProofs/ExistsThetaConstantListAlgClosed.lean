import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin.TorsList

theorem card_torsion_comp {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) {g : ℕ} {K : Type} [Field K]
    {x : Sp K ⟶ S} (hx : PolFib G L g x) {k : Type} [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp K) {n : ℕ}
    (hn : (n : k) ≠ 0) : Nat.card {p : Over.mk (t ≫ x) ⟶ G // p ^ n = 1} = n ^ (2 * g) := by
  obtain ⟨P, α, hg, h, -⟩ := hx
  subst hg
  rw [← GlobalTheory.TorsionCover.card_torsion P.A P.isAb P.smoothDim t hn]
  let Φ := GlobalTheory.ObjPull.pushEquiv h (Over.mk t)
  exact (Nat.card_congr (Φ.toEquiv.subtypeEquiv fun y => by
    rw [← map_eq_one_iff Φ Φ.injective, map_pow]; rfl)).symm

theorem exists_torsion_list : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (g m : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), (m : K) ≠ 0 → PolFib G L g x → ∃ pt : Fin (m ^ (4 * g)) → (Over.mk x ⟶ G), Function.Injective pt ∧ (∀ a, pt a ^ (m ^ 2) = 1) ∧ ∀ (K' : Type) [Field K'] [IsAlgClosed K'] (i : K →+* K') (p : Over.mk (spMap i ≫ x) ⟶ G), p ^ (m ^ 2) = 1 → ∃ a, p.left = spMap i ≫ (pt a).left := by
  intro S G _ _ L g m K _ _ x hm hx
  have hpow : (m ^ 2) ^ (2 * g) = m ^ (4 * g) := by rw [← pow_mul]; congr 1; ring
  have hm2 : ((m ^ 2 : ℕ) : K) ≠ 0 := by push_cast; exact pow_ne_zero _ hm
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
  have hc : Nat.card {p : Over.mk x ⟶ G // p ^ (m ^ 2) = 1} = m ^ (4 * g) := by
    have := card_torsion_comp G L hx (𝟙 (Sp K)) hm2
    rw [Category.id_comp, hpow] at this
    exact this
  have hfin : Finite {p : Over.mk x ⟶ G // p ^ (m ^ 2) = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hm0)
  let e := Finite.equivFinOfCardEq hc
  refine ⟨fun a => (e.symm a).1, fun a b hab => e.symm.injective (Subtype.ext hab), fun a => (e.symm a).2, ?_⟩
  intro K' _ _ i p hp
  have hm' : ((m ^ 2 : ℕ) : K') ≠ 0 := by
    rw [← map_natCast i]; exact (map_ne_zero i).2 hm2
  have hc' := card_torsion_comp G L hx (spMap i) hm'
  rw [hpow] at hc'
  let u : Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl
  have hepi : Epi (spMap i) := Flat.epi_of_flat_of_surjective _
  let F : {q : Over.mk x ⟶ G // q ^ (m ^ 2) = 1} → {q : Over.mk (spMap i ≫ x) ⟶ G // q ^ (m ^ 2) = 1} :=
    fun q => ⟨preHom u q.1, by rw [← map_pow, q.2, map_one]⟩
  have hF : Function.Injective F := by
    intro a b hab
    apply Subtype.ext
    apply Over.OverMorphism.ext
    have h1 : spMap i ≫ a.1.left = spMap i ≫ b.1.left := congrArg (fun z => (Subtype.val z).left) hab
    exact (cancel_epi (spMap i)).1 h1
  have hfin' : Finite {q : Over.mk (spMap i ≫ x) ⟶ G // q ^ (m ^ 2) = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc']; exact pow_ne_zero _ hm0)
  obtain ⟨q, hq⟩ := ((Nat.bijective_iff_injective_and_card F).2 ⟨hF, by rw [hc, hc']⟩).2 ⟨p, hp⟩
  refine ⟨e q, ?_⟩
  show p.left = spMap i ≫ (e.symm (e q)).1.left
  rw [Equiv.symm_apply_apply]
  exact (congrArg (fun z => (Subtype.val z).left) hq).symm

end GlobalTheory.UMin.TorsList
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_list_m_sq_torsion_polarisedFibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (g m : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), (m : K) ≠ 0 → PolFib G L g x → ∃ pt : Fin (m ^ (4 * g)) → (Over.mk x ⟶ G), Function.Injective pt ∧ (∀ a, pt a ^ (m ^ 2) = 1) ∧ ∀ (K' : Type) [Field K'] [IsAlgClosed K'] (i : K →+* K') (p : Over.mk (spMap i ≫ x) ⟶ G), p ^ (m ^ 2) = 1 → ∃ a, p.left = spMap i ≫ (pt a).left := by
  atlas_forward_decl GlobalTheory.UMin.TorsList.exists_torsion_list
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin

theorem exists_thG_of_polFib : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (θ : SecAt G L x) (p : Over.mk x ⟶ G), Odd m → (m : K) ≠ 0 → PolFib G L g x → p ^ (m ^ 2) = 1 → ∃ c : K, ThG G L ρ m θ p (GlobalTheory.ZH.fn c) := by
  intro S G _ _ L ρ hL hρ g m K _ _ x θ p hm hK hP hpm
  obtain ⟨P, α, -, hp, w, hw⟩ := hP
  have hLaw : Laws := GlobalTheory.firstFiveLaws.1
  have hL₁ := P.isLB
  have := P.isAb.comm
  obtain ⟨ρ', hρ', hr⟩ := exists_rigidificationPullbackCompatibleIso hp hw hL hL₁ hρ
  let τ : (baseOver (Sp K)).left ⟶ (Over.mk x).left := 𝟙 (Sp K)
  haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp K)))
  have hτ : τ ≫ (Over.mk x).hom = (baseOver (Sp K)).hom ≫ x := rfl
  have hi : inv τ = 𝟙 (Sp K) := IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
  obtain ⟨q, hq, hqm⟩ := exists_torsion_down hp τ hτ p hpm
  obtain ⟨v, hv⟩ := ThetaPtExist.exists_isThetaPt hLaw K P m hm hK (fun _ : Unit => q) (fun _ => hqm)
  let c' : K := (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (v ())
  have hvc : v = fun _ => GlobalTheory.Ex.fnOf c' := funext fun u =>
    ((Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id_apply (v u)).symm
  rw [hvc] at hv
  obtain ⟨thP, hg, hth⟩ := exists_gen_thG_of_isThetaPt K P ρ' hρ' m Unit (fun _ => q) (fun _ => c') (fun _ => hqm) hv
  obtain ⟨th, hrel⟩ := GlobalTheory.ThetaPtMove.exists_secRel_up hp τ hτ hw hL hL₁ thP
  have hgen := ThetaPtUp.isGenSec_up hp τ hτ hw hL hL₁ hrel hg
  have up := ThG.up hp τ hτ hw hL hL₁ hr hq hpm hrel (hth ())
  rw [hi] at up
  obtain ⟨r, hr'⟩ := hgen θ
  have e₁ : SecM.ofSec G θ = r • SecM.ofSec G th := Subtype.ext (funext hr')
  have q' := ThG.smul hL e₁ up
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (show Γ(Sp K, ⊤) from r) * c', ?_⟩
  convert q' using 1
  simp [GlobalTheory.ZH.fn, GlobalTheory.Ex.fnOf, c']

end GlobalTheory.UMin
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaConstant_m_sq_torsion_algClosed_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (θ : SecAt G L x) (p : Over.mk x ⟶ G), Odd m → (m : K) ≠ 0 → PolFib G L g x → p ^ (m ^ 2) = 1 → ∃ c : K, ThG G L ρ m θ p (GlobalTheory.ZH.fn c) := by
  atlas_forward_decl GlobalTheory.UMin.exists_thG_of_polFib
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem exists_thList : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (θ : SecAt G L x), Odd m → (m : K) ≠ 0 → N = m ^ (4 * g) → PolFib G L g x → ∃ (pt : Fin N → (Over.mk x ⟶ G)) (c : Fin N → K), ThList G L ρ m x θ pt c := by
  intro S G _ _ L ρ hL hρ g m N K _ _ x θ hm hmK hN hP
  subst hN
  obtain ⟨pt, hinj, hpt, hall⟩ := GlobalTheory.T.exists_injective_list_m_sq_torsion_polarisedFibre S G L g m K x hmK hP
  choose c hc using fun a => GlobalTheory.T.exists_thetaConstant_m_sq_torsion_algClosed_fibre S G L ρ hL hρ g m K x θ (pt a) hm hmK hP (hpt a)
  exact ⟨pt, c, hinj, hc, hall⟩

end GlobalTheory.UMin
end
