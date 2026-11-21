import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinBaseChangeP
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.LimAlg
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.ExistsEpsPeriodTUnit
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.PrimOfOver
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.PropsA

section
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison

namespace GlueBL

variable {R : Type} [CommRing R]

theorem lim_sq {A B C D : Sys.{1} R} {σ : R →+* R} (φ : Sys.Hom A B (RingHom.id R)) (ψ : Sys.Hom C D (RingHom.id R))
    (g : Sys.Hom A C σ) (g' : Sys.Hom B D σ) (h : ∀ n x, ψ.f n (g.f n x) = g'.f n (φ.f n x)) (x : A.lim) :
    ψ.lim (g.lim x) = g'.lim (φ.lim x) :=
  Subtype.ext (funext fun n => h n (x.1 n))

variable {Γ Γ' : Type} {S S' : ℕ → Sys.{1} R} {σ : Γ → R →+* R} {σ' : Γ' → R →+* R}
  {act : ∀ j g, Sys.Hom (S j) (S j) (σ g)} {act' : ∀ j g, Sys.Hom (S' j) (S' j) (σ' g)}
  {one : ∀ n, (S 0).M n} {one' : ∀ n, (S' 0).M n}
  {cup : ∀ n i j, (S i).M n → (S j).M n → (S (i + j)).M n} {cup' : ∀ n i j, (S' i).M n → (S' j).M n → (S' (i + j)).M n}

theorem lim_cup (φ : ∀ j, Sys.Hom (S j) (S' j) (RingHom.id R))
    (hc : ∀ n i j x y, (φ (i + j)).f n (cup n i j x y) = cup' n i j ((φ i).f n x) ((φ j).f n y))
    {i j : ℕ} (x : (limAlg S act one cup).N i) (y : (limAlg S act one cup).N j) (z : (limAlg S act one cup).N (i + j))
    (hz : (limAlg S act one cup).cup x y z) :
    (limAlg S' act' one' cup').cup ((φ i).lim x) ((φ j).lim y) ((φ (i + j)).lim z) := fun n =>
  (congrArg ((φ (i + j)).f n) (hz n)).trans (hc n i j _ _)

theorem lim_one (φ : ∀ j, Sys.Hom (S j) (S' j) (RingHom.id R)) (ho : ∀ n, (φ 0).f n (one n) = one' n)
    (x : (limAlg S act one cup).N 0) (hx : (limAlg S act one cup).one x) :
    (limAlg S' act' one' cup').one ((φ 0).lim x) := fun n =>
  (congrArg ((φ 0).f n) (hx n)).trans (ho n)

variable {A B : Sys.{1} R}

theorem lim_inj (φ : Sys.Hom A B (RingHom.id R)) (a u t : R) (N : ℕ) (ht : t = a * u) (h : ∀ n, UpTo (a ^ N) (φ.f n))
    (x : A.lim) (hx : φ.lim x = 0) : t ^ (2 * N) • x = 0 := by
  have h0 : (a ^ N) ^ 2 • x = 0 := (P.lim_upTo φ (a ^ N) h).1 x hx
  have e : t ^ (2 * N) = u ^ (2 * N) * (a ^ N) ^ 2 := by rw [ht]; ring
  rw [e, mul_smul, h0, smul_zero]

theorem lim_surj (φ : Sys.Hom A B (RingHom.id R)) (a u t : R) (N : ℕ) (ht : t = a * u) (h : ∀ n, UpTo (a ^ N) (φ.f n))
    (y : B.lim) : ∃ x, φ.lim x = t ^ (2 * N) • y :=
  Exists.elim ((P.lim_upTo φ (a ^ N) h).2 y) fun x hx =>
    ⟨u ^ (2 * N) • x, by rw [map_smul, hx, smul_smul, ht, mul_pow, mul_comm (a ^ (2 * N)), pow_mul' a]⟩

theorem lim_surj_fil (φ : Sys.Hom A B (RingHom.id R)) (a u t : R) (N : ℕ) (ht : t = a * u)
    (Fil : ∀ n, ℕ → Submodule R (A.M n)) (hsm : ∀ n r, ∀ x ∈ Fil n r, a • x ∈ Fil n (r + 1))
    (hinj : ∀ n x, φ.f n x = 0 → a ^ N • x = 0) (hs : ∀ n y, ∃ x ∈ Fil n N, φ.f n x = a ^ N • y)
    (y : B.lim) : ∃ x : A.lim, (∀ n, x.1 n ∈ Fil n (2 * N)) ∧ φ.lim x = t ^ (2 * N) • y := by
  choose xs hxs hβ using fun n => hs n (y.1 n)
  have hpow : ∀ n (k r : ℕ), ∀ x ∈ Fil n r, a ^ k • x ∈ Fil n (r + k) := by
    intro n k
    induction k with
    | zero => intro r x hx; simpa using hx
    | succ k ih =>
      intro r x hx
      rw [pow_succ', mul_smul, ← add_assoc]
      exact hsm n _ _ (ih r x hx)
  have hc : ∀ n, A.r n (a ^ N • xs (n + 1)) = a ^ N • xs n := by
    intro n
    have h0 : φ.f n (A.r n (xs (n + 1)) - xs n) = 0 := by
      rw [map_sub, ← φ.comm, hβ, hβ, map_smul, y.2 n]
      exact sub_self _
    have h1 := hinj n _ h0
    rw [smul_sub, sub_eq_zero] at h1
    rw [map_smul]
    exact h1
  refine ⟨⟨fun n => u ^ (2 * N) • a ^ N • xs n, fun n => by rw [map_smul, hc]⟩, fun n => ?_, ?_⟩
  · refine Submodule.smul_mem _ _ ?_
    have := hpow n N N (xs n) (hxs n)
    rwa [← two_mul] at this
  · refine Subtype.ext (funext fun n => ?_)
    change φ.f n (u ^ (2 * N) • a ^ N • xs n) = t ^ (2 * N) • y.1 n
    rw [map_smul, map_smul, hβ, smul_smul, smul_smul]
    congr 1
    rw [ht]
    ring

end GlueBL

end CrystallineSemistableComparison
end
end

section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

namespace GlueB'

variable {l : ℕ} [Fact l.Prime]

def βS (hC : B.Compat l) {O : Type} [CommRing O] (F : B.Fn O) (κ : O →+* OC l) (k : Bool) (j : ℕ) :
    Sys.Hom (B.HcSys F κ k j) (MSys (F.pt κ) j) (RingHom.id _) where
  f n := B.β F κ k n j
  comm n x := (hC.red F κ k n.le_succ j x).symm

variable {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem atlas_of {M : Model l K} (h : M.Sm) : ∃ d, Nonempty ((B.schFn M.p).Atlas d) := by
  obtain ⟨hG, hS⟩ := h
  have hP := AdicGeo.proper_p hG
  exact B.P.atlas M.p

variable (Amp : ∀ M : Model l K, E.LineData M.X → Prop)

def bβ (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (j : ℕ) :
    ((dat Amp).H a).N j →ₗ[(per l K).A] ((dat Amp).A a).N j :=
  (βS hC (B.schFn M.p) (okToOC l K) false j).lim

def bβ' (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (j : ℕ) :
    ((dat Amp).H' a).N j →ₗ[(per l K).A] ((dat Amp).A a).N j :=
  (βS hC (B.schFn M.p) (okToOC l K) true j).lim

theorem f_inj (hMain : B.Main l) (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (hM : M.Sm) (j : ℕ) :
    ∃ n : ℕ, ∀ x, bβ Amp hC a j x = 0 → (per l K).t ^ n • x = 0 := by
  obtain ⟨d, ⟨A⟩⟩ := atlas_of hM
  obtain ⟨ε, u, -, ht⟩ := GlueBE.exists_eps_period_t_unit l K
  obtain ⟨N, hN⟩ := hMain d j
  exact ⟨2 * N, fun x hx => GlueBL.lim_inj (βS hC (B.schFn M.p) (okToOC l K) false j) ε.μ u (per l K).t N ht
    (fun n => (hN (B.schFn M.p) (okToOC l K) ε A n).1 false) x hx⟩

theorem f_inj' (hMain : B.Main l) (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (hM : M.Sm) (j : ℕ) :
    ∃ n : ℕ, ∀ x, bβ' Amp hC a j x = 0 → (per l K).t ^ n • x = 0 := by
  obtain ⟨d, ⟨A⟩⟩ := atlas_of hM
  obtain ⟨ε, u, -, ht⟩ := GlueBE.exists_eps_period_t_unit l K
  obtain ⟨N, hN⟩ := hMain d j
  exact ⟨2 * N, fun x hx => GlueBL.lim_inj (βS hC (B.schFn M.p) (okToOC l K) true j) ε.μ u (per l K).t N ht
    (fun n => (hN (B.schFn M.p) (okToOC l K) ε A n).1 true) x hx⟩

theorem f_surj' (hMain : B.Main l) (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (hM : M.Sm) (j : ℕ) :
    ∃ n : ℕ, ∀ y, ∃ x, bβ' Amp hC a j x = (per l K).t ^ n • y := by
  obtain ⟨d, ⟨A⟩⟩ := atlas_of hM
  obtain ⟨ε, u, -, ht⟩ := GlueBE.exists_eps_period_t_unit l K
  obtain ⟨N, hN⟩ := hMain d j
  exact ⟨2 * N, fun y => GlueBL.lim_surj (βS hC (B.schFn M.p) (okToOC l K) true j) ε.μ u (per l K).t N ht
    (fun n => (hN (B.schFn M.p) (okToOC l K) ε A n).1 true) y⟩

theorem f_surj (hMain : B.Main l) (hC : B.Compat l) {M : Model l K} (a : (dat Amp).Ch M) (hM : M.Sm) (j : ℕ) :
    ∃ n : ℕ, ∀ y, ∃ x, (dat Amp).fil a j n x ∧ bβ Amp hC a j x = (per l K).t ^ n • y := by
  obtain ⟨d, ⟨A⟩⟩ := atlas_of hM
  obtain ⟨ε, u, -, ht⟩ := GlueBE.exists_eps_period_t_unit l K
  obtain ⟨N, hN⟩ := hMain d j
  refine ⟨2 * N, fun y => ?_⟩
  obtain ⟨x, hx, hxy⟩ := GlueBL.lim_surj_fil (βS hC (B.schFn M.p) (okToOC l K) false j) ε.μ u (per l K).t N ht
    (fun n r => B.HcFil (B.schFn M.p) (okToOC l K) false n r j)
    (fun n r x hx => hC.smul_fil (B.schFn M.p) (okToOC l K) false n r j ε.μ (ε.μ_mem false (PAlg.base l) n) x hx)
    (fun n x hx => ((hN (B.schFn M.p) (okToOC l K) ε A n).1 false).1 x hx)
    (fun n y => (hN (B.schFn M.p) (okToOC l K) ε A n).2 y) y
  exact ⟨x, hx, hxy⟩

end GlueB'

end CrystallineSemistableComparison
end
end
