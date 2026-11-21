import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaValueTorsionFrame

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ThetaAtRoot

section
variable {S : Scheme.{0}} (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A)))

theorem val_powFrame' {T : Over S} (x : T ⟶ P.A) (e) (k : ℤ) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) (J) :
    val (powFrame P.A P.L x e k) r z J = val e r z J ^ k :=
  map_zpow _ _ _

theorem isThetaConst_of_thG (hrig : rig.IsGen) {m : ℕ} {T : Over S} {th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)}
    {x : T ⟶ P.A} {c : Γ(T.left, ⊤)} (H : ThG P.A P.L rig m th x c) :
    ∃ (s₁ s₂ : LB.Sec (LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) T)) (U : ThetaGrp P.A P.L ((m ^ 2 : ℕ) : ℤ) T),
      GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.IsMulPull P rig m ((m ^ 2 : ℕ) : ℤ) th s₁ ∧ SymLift P.A P.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x U ∧
      IsActOf P.A P.L ((m ^ 2 : ℕ) : ℤ) U s₁ s₂ ∧ GlobalTheory.IndefiniteRowSideFullHecke.UniformityLowerBounds.IsValueZero P rig ((m ^ 2 : ℕ) : ℤ) s₂ c := by
  obtain ⟨-, t, α, s₁, θ, hα, h₂, h₃, h₄, h₅, h₆⟩ := H
  refine ⟨s₁, t, θ, ⟨α, hα, corr_of_val P.isLB fun y J hJ => ?_, h₃⟩, h₄, h₅,
    ⟨rigT P.A P.L rig T ((m ^ 2 : ℕ) : ℤ), GlobalTheory.ThetaReal.NormMul.rigT_isGen hrig _, corr_of_val P.isLB fun _ _ _ => rfl,
      GlobalTheory.ThetaPtMove.isValueAt_of_sv P.isLB fun y J hJ => by rw [Category.id_comp]; exact h₆ y J hJ⟩⟩
  refine (val_corr hJ h₂ (𝟙 _)).trans ?_
  rw [val_mul hJ, val_inv, GlobalTheory.Ex.OneGen.val_rigT _ _ y hJ, GlobalTheory.Ex.OneGen.val_rigT _ _ y hJ,
    GlobalTheory.Ex.OneGen.val_rigT _ _ y hJ, zpow_sub_one, zpow_one]

theorem frame_pull {n : ℕ} {T T₀ : Over S} (u : T ⟶ T₀) {x₀ : T₀ ⟶ P.A}
    {e₀ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => x₀.left) (fun _ => 1))}
    (H : IsTorsFrame P rig n x₀ e₀) :
    IsTorsFrame P rig n (u ≫ x₀) (LB.pullGen P.L (fun _ => x₀.left) (fun _ => 1) e₀ u.left) := by
  obtain ⟨h₁, h₂, α, hα, hN, hc⟩ := H
  refine ⟨by rw [← MonObj.comp_pow, h₁, MonObj.comp_one], LB.isGen_pullGen _ _ _ _ h₂ _, α, hα, hN,
    corr_of_val P.isLB fun y J hJ => ?_⟩
  have q := val_corr hJ hc u.left
  rw [val_powFrame', val_mul hJ, val_pull hJ, GlobalTheory.Ex.OneGen.val_rigT _ _ y hJ, Over.w u] at q
  rw [val_powFrame', val_pull hJ, val_mul hJ, val_pull hJ, GlobalTheory.Ex.OneGen.val_rigT _ _ y hJ, Category.id_comp,
    Category.id_comp, Category.id_comp, Over.comp_left]
  exact q

theorem value_pull {T T₀ : Over S} (u : T ⟶ T₀) {x₀ : T₀ ⟶ P.A}
    {e₀ : LB.Gen (LB.LinComb P.L (Y := T₀.left) (K := Fin 1) (fun _ => x₀.left) (fun _ => 1))}
    {th : LB.Sec (LPow P.A P.L 1 T₀)} {c : Γ(T₀.left, ⊤)} (H : IsValueAt P.A P.L 1 th x₀ e₀ c) :
    IsValueAt P.A P.L 1 (VVRank.pullS P.A 1 u th) (u ≫ x₀)
      (LB.pullGen P.L (fun _ => x₀.left) (fun _ => 1) e₀ u.left) (u.left.appTop.hom c) := by
  refine GlobalTheory.ThetaPtMove.isValueAt_of_sv P.isLB fun y J hJ => ?_
  have e : (ptSecT P.A (u ≫ x₀)) ≫ (u ▷ P.A) = u ≫ ptSecT P.A x₀ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [ptSecT]
  have e' : (𝟙 _ ≫ (ptSecT P.A (u ≫ x₀)).left) ≫ (u ▷ P.A).left = u.left ≫ (ptSecT P.A x₀).left := by
    rw [Category.id_comp, ← Over.comp_left, e, Over.comp_left]
  rw [VVRank.sv_pullS _ _ _ _ _ _ hJ, e', GlobalTheory.ThetaPtMove.sv_of_isValueAt H u.left y hJ, val_pull hJ, Category.id_comp]
  exact congrArg (· * _) (gs_pull (𝟙 _) u.left y ⊤ trivial c).symm

end

end GlobalTheory.ThetaAtRoot

namespace GlobalTheory

open GlobalTheory.ThetaAtRoot in

theorem thetaConst_pow_eq_at_root : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] (i : S.R →+* K) (b : S.Gam) (y : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ ρ.P.A) (v : K), y ^ (S.r * S.N) = (Over.homMk (spMap i) (by simp) : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ baseOver (Sp S.R)) ≫ ρ.pt b → ThG ρ.P.A ρ.P.L ρ.rig (S.r * S.N) (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) y (GlobalTheory.ZH.fn v) → v ^ ((S.r * S.N) ^ 2) = i ⟨S.th b, S.th_mem b⟩ ^ ((S.r * S.N) ^ 2) := by
  intro o Ω _ _ _ _ S ρ K _ i b y v hy H
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hk : Odd (S.r * S.N) := by
    obtain ⟨j, -, hj⟩ := ρ.r_eq
    rw [hj, ρ.N_eq]
    exact ρ.n_odd.pow.mul ρ.n_odd.pow.pow
  let u : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ baseOver (Sp S.R) := Over.homMk (spMap i) (by simp)
  have hfr := frame_pull ρ.P ρ.rig u (ρ.fr_tors b)
  have ht := value_pull ρ.P u (ρ.th_val b)
  obtain ⟨s₁, s₂, U, h₁, hU, hs, h₃⟩ := isThetaConst_of_thG ρ.P ρ.rig ρ.rig_gen H
  let z : Sp K := (⊥ : PrimeSpectrum K)
  obtain ⟨ξ, hξ, e⟩ := GlobalTheory.ThetaCompare.normalised_root_stalk hL.globalFns ρ.P hk hy hfr ht _
    (Nat.cast_pow (S.r * S.N) 2) h₁ hU hs h₃ z
  have ec : u.left.appTop.hom (GlobalTheory.ZH.fn (⟨S.th b, S.th_mem b⟩ : S.R)) = GlobalTheory.ZH.fn (i ⟨S.th b, S.th_mem b⟩) :=
    (congrArg (fun q => q.hom (⟨S.th b, S.th_mem b⟩ : S.R)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom i))).symm
  rw [ec] at e
  let iso := Scheme.ΓSpecIso (CommRingCat.of K)
  let g : K →+* (Sp K).presheaf.stalk z := ((Sp K).presheaf.germ ⊤ z trivial).hom.comp iso.inv.hom
  have hg : Function.Injective g :=
    (germ_injective_of_isIntegral (Sp K) (U := ⊤) z trivial).comp (ConcreteCategory.bijective_of_isIso iso.inv).1
  have hgs : ∀ a : K, gs (𝟙 (Over.mk (spMap i ≫ 𝟙 (Sp S.R))).left) z ⊤ (GlobalTheory.ZH.fn a) = g a :=
    fun a => gs_eq _ z ⊤ trivial _
  apply hg
  rw [map_pow, map_pow, ← hgs, ← hgs, e, mul_pow, ← Units.val_pow_eq_pow_val, hξ, Units.val_one, _root_.one_mul]

end GlobalTheory
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstant_kth_root_labelled_point_up_to_root : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] (i : S.R →+* K) (b : S.Gam) (y : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ ρ.P.A) (v : K), y ^ (S.r * S.N) = (Over.homMk (spMap i) (by simp) : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ baseOver (Sp S.R)) ≫ ρ.pt b → ThG ρ.P.A ρ.P.L ρ.rig (S.r * S.N) (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) y (GlobalTheory.ZH.fn v) → v ^ ((S.r * S.N) ^ 2) = i ⟨S.th b, S.th_mem b⟩ ^ ((S.r * S.N) ^ 2) := by
  atlas_forward_decl GlobalTheory.thetaConst_pow_eq_at_root
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.RealTh

theorem exists_pow_eq (hL : Laws) {S : Scheme.{0}} (P : PolAV S) {K : Type} [Field K] [IsAlgClosed K] (x : Sp K ⟶ S)
    {k : ℕ} (hk : (k : K) ≠ 0) (z : Over.mk x ⟶ P.A) (hz : z ^ k = 1) : ∃ y : Over.mk x ⟶ P.A, y ^ k = z := by
  have := P.isAb.comm
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; exact hk Nat.cast_zero)
  have hk2 : ((k ^ 2 : ℕ) : K) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hk
  have c₁ := TorsionFieldExt.card_torsion hL P x hk
  have c₂ := TorsionFieldExt.card_torsion hL P x hk2
  let H₁ := (powMonoidHom k : (Over.mk x ⟶ P.A) →* (Over.mk x ⟶ P.A)).ker
  let H₂ := (powMonoidHom (k ^ 2) : (Over.mk x ⟶ P.A) →* (Over.mk x ⟶ P.A)).ker
  have e₁ : Nat.card H₁ = k ^ (2 * P.g) :=
    (Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp [H₁, MonoidHom.mem_ker])).trans c₁
  have e₂ : Nat.card H₂ = (k ^ 2) ^ (2 * P.g) :=
    (Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp [H₂, MonoidHom.mem_ker])).trans c₂
  have : Finite H₂ := Nat.finite_of_card_ne_zero (by rw [e₂]; positivity)
  have : Finite H₁ := Nat.finite_of_card_ne_zero (by rw [e₁]; positivity)
  let ψ : H₂ →* (Over.mk x ⟶ P.A) := (powMonoidHom k).comp H₂.subtype
  have hker : Nat.card ψ.ker = k ^ (2 * P.g) := by
    rw [← e₁]
    refine Nat.card_congr (Equiv.ofBijective (fun y => ⟨y.1.1, ?_⟩) ⟨fun a b h => ?_, fun a => ?_⟩)
    · exact MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 y.2)
    · apply Subtype.ext; apply Subtype.ext; exact congrArg (fun q : H₁ => (q : Over.mk x ⟶ P.A)) h
    · refine ⟨⟨⟨a.1, ?_⟩, ?_⟩, rfl⟩
      · have := a.2
        simp only [H₁, MonoidHom.mem_ker, powMonoidHom_apply] at this
        simp [H₂, MonoidHom.mem_ker, sq, pow_mul, this]
      · exact MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 a.2)
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hker, e₂, ← pow_mul, mul_comm 2, pow_mul,
    sq, mul_comm] at hmul
  have hrange : Nat.card ψ.range = Nat.card H₁ := by
    rw [e₁]
    exact (Nat.eq_of_mul_eq_mul_right (by positivity) hmul).symm
  have hle : ψ.range ≤ H₁ := by
    rintro _ ⟨y, rfl⟩
    have := y.2
    simp only [H₂, MonoidHom.mem_ker, powMonoidHom_apply] at this
    simp [ψ, H₁, MonoidHom.mem_ker, ← pow_mul, ← sq, this]
  have heq := Subgroup.eq_of_le_of_card_ge hle hrange.ge
  have hzm : z ∈ ψ.range := heq ▸ (show z ∈ H₁ by simpa [H₁, MonoidHom.mem_ker] using hz)
  obtain ⟨y, hy⟩ := hzm
  exact ⟨y.1, hy⟩

end GlobalTheory.UMin.RealTh

open GlobalTheory.UMin.RealTh in

theorem GlobalTheory.UMin.thList_real : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] (i : S.R →+* K) (N : ℕ) (pt : Fin N → (Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ ρ.P.A)) (c : Fin N → K), ThList ρ.P.A ρ.P.L ρ.rig (S.r * S.N) (spMap i ≫ 𝟙 (Sp S.R)) (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) pt c → (∀ x, ∃ b, c x ^ ((S.r * S.N) ^ 2) = i ⟨S.th b, S.th_mem b⟩ ^ ((S.r * S.N) ^ 2)) ∧ ∀ b, ∃ x, c x ^ ((S.r * S.N) ^ 2) = i ⟨S.th b, S.th_mem b⟩ ^ ((S.r * S.N) ^ 2) := by
  intro o Ω _ _ _ _ S ρ K _ i N pt c H
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hkK : ((S.r * S.N : ℕ) : K) ≠ 0 := by
    have := S.unit.map (i.comp (algebraMap o S.R))
    rw [map_natCast] at this
    exact this.ne_zero
  let β : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ baseOver (Sp S.R) := Over.homMk (spMap i) (by simp)
  let j : K →+* AlgebraicClosure K := algebraMap _ _
  let u : Over.mk (spMap j ≫ spMap i ≫ 𝟙 (Sp S.R)) ⟶ Over.mk (spMap i ≫ 𝟙 (Sp S.R)) := Over.homMk (spMap j) rfl
  have hkK' : ((S.r * S.N : ℕ) : AlgebraicClosure K) ≠ 0 := by
    rw [← map_natCast j]; exact (map_ne_zero j).2 hkK
  have down : ∀ y : Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ ρ.P.A, y ^ (S.r * S.N) = 1 → ∃ b, y = β ≫ ρ.pt b := by
    intro y hy
    obtain ⟨b, hb, -⟩ := ρ.pt_bij (AlgebraicClosure K) (spMap j ≫ spMap i ≫ 𝟙 _) (u ≫ y)
      (by rw [← MonObj.comp_pow, hy, MonObj.comp_one])
    refine ⟨b, TorsionFieldExt.comp_injective u _ ?_⟩
    refine hb.symm.trans (Over.OverMorphism.ext ?_)
    simp [u, β]
  constructor
  · intro x
    have h := H.2.1 x
    obtain ⟨b, hb⟩ := down (pt x ^ (S.r * S.N)) (by rw [← pow_mul, ← sq]; exact h.1)
    exact ⟨b, GlobalTheory.T.thetaConstant_kth_root_labelled_point_up_to_root o Ω S ρ K i b (pt x) (c x) hb h⟩
  · intro b
    have tb : ρ.pt b ^ (S.r * S.N) = 1 := (ρ.fr_tors b).1
    obtain ⟨y, hy⟩ := exists_pow_eq hL ρ.P (spMap j ≫ spMap i ≫ 𝟙 _) hkK' (u ≫ β ≫ ρ.pt b)
      (by rw [← MonObj.comp_pow, ← MonObj.comp_pow, tb, MonObj.comp_one, MonObj.comp_one])
    obtain ⟨a, ha⟩ := H.2.2 (AlgebraicClosure K) j y
      (by rw [sq, pow_mul, hy, ← MonObj.comp_pow, ← MonObj.comp_pow, tb, MonObj.comp_one, MonObj.comp_one])
    have e1 : u ≫ pt a = y := Over.OverMorphism.ext ha.symm
    have e2 : pt a ^ (S.r * S.N) = β ≫ ρ.pt b :=
      TorsionFieldExt.comp_injective u _ (by
        show u ≫ _ = u ≫ _
        rw [MonObj.comp_pow, e1, hy])
    exact ⟨a, GlobalTheory.T.thetaConstant_kth_root_labelled_point_up_to_root o Ω S ρ K i b (pt a) (c a) e2 (H.2.1 a)⟩
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstantList_realisedSystem_up_to_rootsOfUnity : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] (i : S.R →+* K) (N : ℕ) (pt : Fin N → (Over.mk (spMap i ≫ 𝟙 (Sp S.R)) ⟶ ρ.P.A)) (c : Fin N → K), ThList ρ.P.A ρ.P.L ρ.rig (S.r * S.N) (spMap i ≫ 𝟙 (Sp S.R)) (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) pt c → (∀ x, ∃ b, c x ^ ((S.r * S.N) ^ 2) = i ⟨S.th b, S.th_mem b⟩ ^ ((S.r * S.N) ^ 2)) ∧ ∀ b, ∃ x, c x ^ ((S.r * S.N) ^ 2) = i ⟨S.th b, S.th_mem b⟩ ^ ((S.r * S.N) ^ 2) := by
  atlas_forward_decl GlobalTheory.UMin.thList_real
end
