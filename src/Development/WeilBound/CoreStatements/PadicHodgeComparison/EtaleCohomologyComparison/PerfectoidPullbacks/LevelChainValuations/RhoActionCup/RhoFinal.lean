import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.RhoActionCup.RHofTrGen
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.CupGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationCupProduct
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.RHofLev
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.fil_lev
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ValuationChainProofs.CrystallineFirstChernLevelCompat
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.HomSGood
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.HomGalGood
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.GaloisCupProducts.HomPullRHofGood
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.ExistsLim
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRealizationOfCompatible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationAdd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationSmul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationFunctorial
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealizationUnitClass
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.LatLink

section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
theorem cup_genA {m : ℕ} {L : Lev (per l K) m} (hL : L.Good) (M : Model l K) (s : ℕ)
    (hQ : ∀ T, QB L M s T → QA L M s (((nmB M hL).mor 0).obj T))
    (rH : ∀ n j, M.Hc false n j →ₛₗ[L.lam] HM (QA L M s) none ((l : L.A) ^ n) j) (hG : (chainOf hL M s hQ rH).Good)
    (hP : (cupOf hL M s hQ rH).Good) {i j : ℕ} (x : ∀ n, M.Hc false n i) (y : ∀ n, M.Hc false n j) (z : ∀ n, M.Hc false n (i + j))
    (f : Module.Dual K (HdR M.q i) →+ L.B) (g : Module.Dual K (HdR M.q j) →+ L.B) (h : Module.Dual K (HdR M.q (i + j)) →+ L.B)
    (hx : (chainOf hL M s hQ rH).Rho x f) (hy : (chainOf hL M s hQ rH).Rho y g) (hz : (chainOf hL M s hQ rH).Rho z h)
    (hc : ∀ n, z n = cupS M n i j (x n) (y n)) {e e' : ℕ} (b : Module.Basis (Fin e) K (HdR M.q i))
    (b' : Module.Basis (Fin e') K (HdR M.q j)) (φ : Module.Dual K (HdR M.q (i + j))) :
    h φ = ∑ s, ∑ s', f (b.coord s) * g (b'.coord s') * algebraMap K L.B (φ (cupK M.q rfl (b s) (b' s'))) := by
  obtain rfl : z = fun n => cupS M n i j (x n) (y n) := funext hc
  have H : h φ = ∑ s, ∑ s', f (b.coord s) * g (b'.coord s') * algebraMap K L.B (φ (cupR M i j (b s) (b' s'))) :=
    GlobalTheory.T.realization_cup_product (chainOf hL M s hQ rH) hG (cupOf hL M s hQ rH) hP x y f g h hx hy hz b b' φ
  simp only [cupR_eq] at H
  exact H

end CrystallineSemistableComparison.Pb.Kap
end
end

section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap.Mo

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
variable (S : LevSys (per l K)) (hS : S.Good) (hC : ∀ m, (S.L m).CrisOK)

variable [FiniteDimensional ℚ_[l] K]

theorem chK_good (M : Model l K) (hM : M.Sm) (m : ℕ) :
    ∃ s₁, ∀ s, s₁ ≤ s → (chK S hS hC M m s).Good := by
  obtain ⟨U⟩ := cov_sm_pf M hM
  refine ⟨Finset.univ.sup U.d + (m + 1), fun s hs => ?_⟩
  refine chain_good (hS.lev m) M s hM U (fun α => ?_) (by omega) _ (rHof_tr_gen _ _ M s)
  have := Finset.le_sup (f := U.d) (Finset.mem_univ α)
  omega

theorem rho_mono (M : Model l K) (m : ℕ) {s s' : ℕ} (h : s ≤ s') (hG : (chK S hS hC M m s).Good)
    (hG' : (chK S hS hC M m s').Good) {j : ℕ} (x : ∀ n, M.Hc false n j) (f : Module.Dual K (HdR M.q j) →+ (S.L m).B)
    (hf : (chK S hS hC M m s').Rho x f) : (chK S hS hC M m s).Rho x f := by
  have H := GlobalTheory.T.realization_functorial (chK S hS hC M m s') (chK S hS hC M m s)
    (homS (hS.lev m) M h (qb_le (hS.lev m) M s) (qb_le (hS.lev m) M s')
      (rHof (dOf S hS hC m) (hcOf S hS hC m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s'))
    hG' hG (homS_good_of_inclHM _ _ _ _ _ _ _ (rHof_incl_pf S hS hC M m h)) x f hf
  have e : (homS (hS.lev m) M h (qb_le (hS.lev m) M s) (qb_le (hS.lev m) M s')
      (rHof (dOf S hS hC m) (hcOf S hS hC m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s')).tr j f = f := by
    ext φ
    rfl
  rw [e] at H
  exact H

theorem rho_uniq_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m x f f',
    rhoK S hS hC a j m x f → rhoK S hS hC a j m x f' → f = f' := by
  intro M a hM j m x f f' ⟨_, s₀, h⟩ ⟨_, s₀', h'⟩
  obtain ⟨s₁, hg⟩ := chK_good S hS hC M hM m
  exact GlobalTheory.T.realization_unique (chK S hS hC M m (max s₁ (max s₀ s₀'))) (hg _ (le_max_left _ _)) _ f f'
    (h _ (le_trans (le_max_left _ _) (le_max_right _ _))) (h' _ (le_trans (le_max_right _ _) (le_max_right _ _)))

theorem rho_ex_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m x, ∃ f, rhoK S hS hC a j m x f := by
  intro M a hM j m x
  obtain ⟨s₁, hg⟩ := chK_good S hS hC M hM m
  obtain ⟨f, hf⟩ := GlobalTheory.T.exists_realization_of_compatible (chK S hS hC M m s₁) (hg s₁ le_rfl) (show (M.HS false j).lim from x).1
    (fun n => (show (M.HS false j).lim from x).2 n)
  refine ⟨f, hM, s₁, fun s hs => ?_⟩
  obtain ⟨g, hgs⟩ := GlobalTheory.T.exists_realization_of_compatible (chK S hS hC M m s) (hg s hs) (show (M.HS false j).lim from x).1
    (fun n => (show (M.HS false j).lim from x).2 n)
  have e : g = f := GlobalTheory.T.realization_unique _ (hg s₁ le_rfl) _ g f (rho_mono S hS hC M m hs (hg s₁ le_rfl) (hg s hs) _ g hgs) hf
  rwa [e] at hgs

theorem rho_add_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m x y f g,
    rhoK S hS hC a j m x f → rhoK S hS hC a j m y g → rhoK S hS hC a j m (x + y) (f + g) := by
  intro M a hM j m x y f g ⟨_, s₀, h⟩ ⟨_, s₀', h'⟩
  exact ⟨hM, max s₀ s₀', fun s hs => GlobalTheory.T.realization_add (chK S hS hC M m s) _ _ f g
    (h s (le_trans (le_max_left _ _) hs)) (h' s (le_trans (le_max_right _ _) hs))⟩

theorem rho_smul_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m (c : (per l K).A) x f, rhoK S hS hC a j m x f →
    rhoK S hS hC a j m (c • x) ((AddMonoidHom.mulLeft ((S.L m).ι ((S.L m).lam c))).comp f) := by
  intro M a hM j m c x f ⟨_, s₀, h⟩
  exact ⟨hM, s₀, fun s hs => GlobalTheory.T.realization_smul (chK S hS hC M m s) c _ f (h s hs)⟩

theorem rho_lin'_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m x f, rhoK S hS hC a j m x f →
    ∀ (k : K) φ, f (k • φ) = algebraMap K (S.L m).B k * f φ := by
  intro M a hM j m x f ⟨_, s₀, h⟩ k φ
  exact (h s₀ le_rfl).1 k φ

theorem rho_fil_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m x f, rhoK S hS hC a j m x f → ∀ n r : ℕ, n ≤ m →
    (dat Amp).fil a j n x → ∀ φ : Module.Dual K (HdR M.q j), (∀ h ∈ FilR M.q j (r + 1), φ h = 0) →
      f φ ∈ pdP (S.L m).γB (n - r) := by
  intro M a hM j m x f ⟨_, s₀, h⟩ n r hnm hfil φ hφ
  obtain ⟨U⟩ := cov_sm_pf M hM
  have hU : ∀ α, U.d α + (m + 1) ≤ max s₀ (Finset.univ.sup U.d + (m + 1)) := fun α => by
    have := Finset.le_sup (f := U.d) (Finset.mem_univ α)
    omega
  exact fil_lev_pf (hS.lev m) (dOf S hS hC m) (hcOf S hS hC m) M _ hM U hU (by omega) _
    (fun n => (show (M.HS false j).lim from x).2 n) f (h _ (le_max_left _ _)) n r (by omega) hfil φ hφ

theorem rho_firstChern_formula : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ m x f c, rhoK S hS hC a 2 m x f → (dat Amp).c1H a x →
    IsFirstChernDeRham _ (lineK a.1) c → ∀ φ, f φ = algebraMap K (S.L m).B (φ c) := by
  intro M a hM m x f c ⟨_, s₀, h⟩ hx hc φ
  obtain ⟨U⟩ := cov_sm_pf M hM
  obtain ⟨s₁, hg⟩ := chK_good S hS hC M hM m
  have hU : ∀ α, U.d α + (m + 1) ≤ max (max s₀ s₁) (Finset.univ.sup U.d + (m + 1)) := fun α => by
    have := Finset.le_sup (f := U.d) (Finset.mem_univ α)
    omega
  have H := crystalline_firstChern_level (hS.lev m) (dOf S hS hC m) (hcOf S hS hC m) M _ hM U hU (by omega) a x hx c hc
  have e := GlobalTheory.T.realization_unique (chK S hS hC M m _) (hg _ (by omega)) _ f (evB M c) (h _ (by omega)) H
  rw [e]
  rfl

end CrystallineSemistableComparison.Pb.Kap.Mo
end
end

section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap.Mo

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
variable (S : LevSys (per l K)) (hS : S.Good) (hC : ∀ m, (S.L m).CrisOK)

variable [FiniteDimensional ℚ_[l] K]

theorem lev_good (M : Model l K) (m s : ℕ) : (homLev S hS m M s (qb_le (hS.lev (m + 1)) M s) (qb_le (hS.lev m) M s)
    (rHof (dOf S hS hC (m + 1)) (hcOf S hS hC (m + 1)) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s)).Good where
  ℓ := rfl
  lam c := hS.dlam m c
  ι a := hS.dι m a
  o k := hS.dK m k
  tS n j x := rfl
  r n j x := nmHM_nmLevA_rHof_succ S hS hC M m s n j x
  red n j z := nmHM_redM _ l s none n j z
  b j z := nmHO_nmLevB_bMap S hS m M s _ _ j z
  μ j v := (nm_muB (nmLevB S hS m M) (Category.id_comp _) 1 s (hS.dK m) j v).trans (congrArg _ (pullR_id' M.q j v))

theorem rho_lev_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m x f,
    rhoK S hS hC a j (m + 1) x f → rhoK S hS hC a j m x ((S.dB m).toAddMonoidHom.comp f) := by
  intro M a hM j m x f ⟨hM', s₀, hs₀⟩
  refine ⟨hM', ?_⟩
  obtain ⟨s₁, hs₁⟩ := chK_good S hS hC M hM (m + 1)
  obtain ⟨s₂, hs₂⟩ := chK_good S hS hC M hM m
  refine ⟨max s₀ (max s₁ s₂), fun s hs => ?_⟩
  have h := GlobalTheory.T.realization_functorial (chK S hS hC M (m + 1) s) (chK S hS hC M m s)
    (homLev S hS m M s (qb_le (hS.lev (m + 1)) M s) (qb_le (hS.lev m) M s)
      (rHof (dOf S hS hC (m + 1)) (hcOf S hS hC (m + 1)) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s))
    (hs₁ s (by omega)) (hs₂ s (by omega)) (lev_good S hS hC M m s)
    (show (M.HS false j).lim from x).1 f (hs₀ s (by omega))
  exact h

theorem rho_act_of (hG : ∀ (M : Model l K) m s g, (homGal (hS.lev m) g M s (qb_le (hS.lev m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s)).Good) : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m (g : K.fixingSubgroup) x f,
    rhoK S hS hC a j m x f → rhoK S hS hC a j m (((dat Amp).H a).act j g x) (((S.L m).σB g).toAddMonoidHom.comp f) := by
  intro M a hM j m g x f ⟨hM', s₀, hs₀⟩
  obtain ⟨s₁, hs₁⟩ := chK_good S hS hC M hM m
  refine ⟨hM', max s₀ s₁, fun s hs => ?_⟩
  exact GlobalTheory.T.realization_functorial (chK S hS hC M m s) (chK S hS hC M m s) (homGal (hS.lev m) g M s (qb_le (hS.lev m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s))
    (hs₁ s (by omega)) (hs₁ s (by omega)) (hG M m s g) (show (M.HS false j).lim from x).1 f (hs₀ s (by omega))

theorem rho_nat_of (hP : ∀ (M N : Model l K) (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) m s,
    (homPull (hS.lev m) u hu s (qb_le (hS.lev m) N s) (qb_le (hS.lev m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) N s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s)).Good) : ∀ {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p} {a : (dat Amp).Ch M} {b : (dat Amp).Ch N}
    (μ : (dat Amp).Mo u hu a b), M.Sm → N.Sm → ∀ j m x f f', rhoK S hS hC b j m x f → rhoK S hS hC a j m ((dat Amp).pullH μ j x) f' →
      ∀ φ, f' φ = f (φ ∘ₗ pullR j (Model.genMap u hu) (Model.genMap_q u hu)) := by
  intro M N u hu a b μ hM hN j m x f f' ⟨_, s₀, h₀⟩ ⟨_, s₀', h₀'⟩ φ
  obtain ⟨s₁, hs₁⟩ := chK_good S hS hC M hM m
  obtain ⟨s₂, hs₂⟩ := chK_good S hS hC N hN m
  obtain ⟨s, e0, e1, e2, e3⟩ : ∃ s, s₀ ≤ s ∧ s₀' ≤ s ∧ s₁ ≤ s ∧ s₂ ≤ s := ⟨s₀ + s₀' + s₁ + s₂, by omega⟩
  have h := GlobalTheory.T.realization_functorial (chK S hS hC N m s) (chK S hS hC M m s) _ (hs₂ s e3) (hs₁ s e2) (hP M N u hu m s)
    (show (N.HS false j).lim from x).1 f (h₀ s e0)
  have e := GlobalTheory.T.realization_unique (chK S hS hC M m s) (hs₁ s e2) _ f' _ (h₀' s e1) h
  rw [e]
  rfl

theorem rho_one_of (hU : ∀ (M : Model l K) m s, (cupOf (hS.lev m) M s (qb_le (hS.lev m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s)).Good) : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ m x f, rhoK S hS hC a 0 m x f → ((dat Amp).H a).one x →
    ∀ φ, f φ = algebraMap K (S.L m).B (φ (oneK M.q)) := by
  intro M a hM m x f ⟨_, s₀, h₀⟩ hx φ
  obtain ⟨s₁, hs₁⟩ := chK_good S hS hC M hM m
  obtain ⟨s, e0, e1⟩ : ∃ s, s₀ ≤ s ∧ s₁ ≤ s := ⟨s₀ + s₁, by omega⟩
  have h := h₀ s e0
  rw [show (show (M.HS false 0).lim from x).1 = (cupOf (hS.lev m) M s (qb_le (hS.lev m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s)).oneS from
    funext ((one_iff (hS.lev m) M s (qb_le (hS.lev m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s) a x).1 hx)] at h
  exact GlobalTheory.T.realization_unit_class (chK S hS hC M m s) (hs₁ s e1) _ (hU M m s) f h φ

theorem rho_cup_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ {i j : ℕ} m x y z f g h,
    rhoK S hS hC a i m x f → rhoK S hS hC a j m y g → rhoK S hS hC a (i + j) m z h → ((dat Amp).H a).cup x y z →
    ∀ {e e' : ℕ} (b : Module.Basis (Fin e) K (HdR M.q i)) (b' : Module.Basis (Fin e') K (HdR M.q j))
      (φ : Module.Dual K (HdR M.q (i + j))),
      h φ = ∑ s, ∑ s', f (b.coord s) * g (b'.coord s') * algebraMap K (S.L m).B (φ (cupK M.q rfl (b s) (b' s'))) := by
  intro M a hM i j m x y z f g h hx hy hz hc e e' b b' φ
  refine hx.2.elim fun s₀ h₀ => hy.2.elim fun s₁ h₁ => hz.2.elim fun s₂ h₂ => (chK_good S hS hC M hM m).elim fun s₃ h₃ => ?_
  exact cup_genA (hS.lev m) M (s₀ + s₁ + s₂ + s₃) _ _ (h₃ _ (by omega)) (cupOf_rHof_good _ M _ _ _ _) _ _ _ f g h (h₀ _ (by omega))
    (h₁ _ (by omega)) (h₂ _ (by omega))
    ((cup_iff_cS_lim (hS.lev m) M 0 (qb_le (hS.lev m) M 0) (rHof (dOf S hS hC m) (hcOf S hS hC m) M 0) a x y z).1 hc) b b' φ

include hS hC in
theorem rhoSys_ex : Nonempty (RhoSys S Model.Sm (dat Amp) fun a c => IsFirstChernDeRham _ (lineK a.1) c) :=
  ⟨{ ρ := rhoK S hS hC
     ex := rho_ex_pf S hS hC
     uniq := rho_uniq_pf S hS hC
     add := rho_add_pf S hS hC
     smul := rho_smul_pf S hS hC
     lin' := rho_lin'_pf S hS hC
     lev := rho_lev_pf S hS hC
     act := rho_act_of S hS hC fun M m s g => homGal_good_of_galRed _ g M s _ _ (galRed_rHof _ _ _ g M s)
     nat := rho_nat_of S hS hC fun M N u hu m s => homPull_rHof_good _ _ u hu s _ _ _
     fil := rho_fil_pf S hS hC
     cup := rho_cup_pf S hS hC
     one := rho_one_of S hS hC fun M m s => cupOf_rHof_good _ M s _ _ _
     c1 := rho_firstChern_formula S hS hC }⟩

theorem crystalline_deRham_firstChern_exists : ∃ L : KapL (l := l) (K := K) Amp, LieComplementChartContDiffAt L := by
  obtain ⟨S, hS, hC⟩ := CrystallineSemistableComparison.HT.levSys_ex (l := l) (K := K)
  obtain ⟨P⟩ := rhoSys_ex S hS hC
  obtain ⟨A⟩ := kap_abs (facts l K) (fun c => ⟨_, rfl⟩) hS P
  exact ⟨⟨A.κ, A.lin, A.lin', A.act, A.nat, A.fil, A.cup, A.one⟩, A.c1⟩

end CrystallineSemistableComparison.Pb.Kap.Mo
end
end
