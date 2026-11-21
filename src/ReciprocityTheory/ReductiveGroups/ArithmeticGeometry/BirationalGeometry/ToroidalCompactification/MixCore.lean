import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.WeilRos

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U]

variable (A U) in

@[ext] structure Th where

  x : A

  f : A → U

instance : Monoid (Th A U) where
  mul g h := ⟨g.x * h.x, fun y => g.f y * h.f (y * g.x)⟩
  one := ⟨1, fun _ => 1⟩
  mul_assoc g h k := Th.ext (_root_.mul_assoc _ _ _) (funext fun y => by
    show g.f y * h.f (y * g.x) * k.f (y * (g.x * h.x)) = g.f y * (h.f (y * g.x) * k.f (y * g.x * h.x))
    rw [_root_.mul_assoc, _root_.mul_assoc y])
  one_mul g := Th.ext (_root_.one_mul _) (funext fun y => by show 1 * g.f (y * 1) = _; rw [_root_.one_mul, _root_.mul_one])
  mul_one g := Th.ext (_root_.mul_one _) (funext fun y => _root_.mul_one _)

theorem Th.adapted_frame_mul_vecMulVec (g h : Th A U) : (g * h).x = g.x * h.x := rfl
theorem Th.mul_f (g h : Th A U) (y : A) : (g * h).f y = g.f y * h.f (y * g.x) := rfl

theorem Th.theta_pow_x (g : Th A U) (n : ℕ) : (g ^ n).x = g.x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ n ih => rw [pow_succ, pow_succ, Th.adapted_frame_mul_vecMulVec, ih]

theorem Th.pow_f (g : Th A U) (n : ℕ) (y : A) : (g ^ n).f y = ∏ j ∈ Finset.range n, g.f (y * g.x ^ j) := by
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih => rw [pow_succ, Th.mul_f, ih, Th.theta_pow_x, Finset.prod_range_succ]

structure Th.Sym (ν : A → U) (N : ℕ) (g : Th A U) : Prop where
  pow : g ^ N = 1
  sym : ∀ y, g.f (y * g.x⁻¹) * ν y * g.f y⁻¹ = ν (y * g.x⁻¹)

variable {ν ν' : A → U} {N : ℕ} {g h : Th A U}

theorem Th.Sym.of_dvd {N' : ℕ} (s : g.Sym ν N) (d : N ∣ N') : g.Sym ν N' := ⟨by obtain ⟨r, rfl⟩ := d; rw [pow_mul, s.pow, one_pow], s.sym⟩

theorem Th.Sym.mul (s : g.Sym ν N) (t : h.Sym ν N) (c : Commute g h) : (g * h).Sym ν N := by
  refine ⟨by rw [c.mul_pow, s.pow, t.pow, _root_.mul_one], fun y => ?_⟩
  have a₁ := congrArg Additive.ofMul (s.sym y)
  have a₂ := congrArg Additive.ofMul (t.sym (y * g.x⁻¹))
  have a₃ := congrArg (fun q : Th A U => Additive.ofMul (q.f (y * g.x⁻¹ * h.x⁻¹))) c.eq
  have e₁ : y * (g.x * h.x)⁻¹ = y * g.x⁻¹ * h.x⁻¹ := by rw [mul_inv, _root_.mul_assoc]
  have e₂ : (y * g.x⁻¹)⁻¹ = y⁻¹ * g.x := by rw [mul_inv, inv_inv]
  apply Additive.ofMul.injective
  simp only [Th.mul_f, Th.adapted_frame_mul_vecMulVec, e₁, e₂, inv_mul_cancel_right, ofMul_mul] at a₁ a₂ a₃ ⊢
  linear_combination (norm := abel) a₁ + a₂ + a₃

theorem Th.Sym.unique (hN : Odd N) (s : g.Sym ν N) (t : h.Sym ν N) (ex : g.x = h.x) {c : U} (e : ∀ y, g.f y = c * h.f y) :
    g = h := by
  have p : c ^ N = 1 := by
    have a := congrArg (fun q : Th A U => q.f 1) s.pow
    have b := congrArg (fun q : Th A U => q.f 1) t.pow
    simp only [Th.pow_f, e, ex, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range] at a b
    rw [b] at a; exact (_root_.mul_one _).symm.trans a
  have q : c ^ 2 = 1 := by
    have a := congrArg Additive.ofMul (s.sym 1)
    have b := congrArg Additive.ofMul (t.sym 1)
    apply Additive.ofMul.injective
    simp only [e, ex, ofMul_mul, ofMul_pow, ofMul_one] at a b ⊢
    linear_combination (norm := abel) a - b
  obtain ⟨m, rfl⟩ := hN
  rw [pow_succ, pow_mul, q, one_pow, _root_.one_mul] at p
  exact Th.ext ex (funext fun y => by rw [e, p, _root_.one_mul])

def Th.pull (f : A →* A) (δ : A → U) (x : A) (g : Th A U) : Th A U := ⟨x, fun y => δ y * g.f (f y) * (δ (y * x))⁻¹⟩

theorem Th.Sym.pull (s : g.Sym ν N) (f : A →* A) (δ : A → U) {x : A} (hx : f x = g.x) (hN : x ^ N = 1) {κ : U}
    (hν : ∀ y, ν' y = κ * (δ y * (δ y⁻¹)⁻¹ * ν (f y))) : (g.pull f δ x).Sym ν' N := by
  have tel : ∀ n y, ((g.pull f δ x) ^ n).f y = δ y * (g ^ n).f (f y) * (δ (y * x ^ n))⁻¹ := fun n y => by
    induction n with
    | zero => rw [pow_zero, pow_zero, pow_zero, _root_.mul_one]; show 1 = δ y * 1 * _; simp
    | succ n ih =>
      rw [pow_succ, pow_succ g, Th.mul_f, Th.mul_f, ih, Th.theta_pow_x, Th.theta_pow_x, pow_succ, ← _root_.mul_assoc y, ← hx, ← map_pow,
        ← map_mul]
      apply Additive.ofMul.injective
      simp only [Th.pull, ofMul_mul, ofMul_inv]
      abel
  refine ⟨Th.ext ((Th.theta_pow_x _ _).trans hN) (funext fun y => ?_), fun y => ?_⟩
  · rw [tel, s.pow, hN, _root_.mul_one]; show δ y * 1 * _ = 1; simp
  · have a := congrArg Additive.ofMul (s.sym (f y))
    have e₂ : (y * x⁻¹)⁻¹ = y⁻¹ * x := by rw [mul_inv, inv_inv]
    apply Additive.ofMul.injective
    simp only [Th.pull, hν, e₂, inv_mul_cancel_right, map_mul, map_inv, hx, ofMul_mul, ofMul_inv] at a ⊢
    linear_combination (norm := abel) a

theorem Th.sym_one : (1 : Th A U).Sym ν N := ⟨one_pow _, fun y => by show 1 * ν y * 1 = ν (y * 1⁻¹); simp⟩

theorem Th.commute_of {θ : A → A → A → U} (C : IsCub θ) {k : ℕ} (hg : g.x ^ k = 1) (hh : h.x ^ k = 1)
    (eg : ∀ y, g.f y = g.f 1 * cubN θ k 1 g.x y) (eh : ∀ y, h.f y = h.f 1 * cubN θ k 1 h.x y)
    (e : cubN θ k 1 g.x h.x = cubN θ k 1 h.x g.x) : Commute g h :=
  Th.ext (mul_comm _ _) (funext fun y => by
    have a₁ := congrArg Additive.ofMul (cubN_right C hg y h.x)
    have a₂ := congrArg Additive.ofMul (cubN_right C hh y g.x)
    have a₃ := congrArg Additive.ofMul e
    rw [C.s01, C.s12, C.s01] at a₂
    rw [Th.mul_f, Th.mul_f, eg y, eh y, eg (y * _), eh (y * _)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul] at a₁ a₂ a₃ ⊢
    linear_combination (norm := abel) a₂ - a₁ - a₃)

end Alg

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} {T T' : Over S} (σ : T' ⟶ T) (z : T'.left)
  (J : (T'.left ⟶ A.left) → L.L.ι)

def IsGeo (k : ℕ) (x : T ⟶ A) (g : Th (T' ⟶ A) (T'.left.presheaf.stalk z)ˣ) : Prop :=
  g.x = σ ≫ x ∧ ∃ (K : Type) (_ : Fintype K) (φ : K → ((T ⊗ A).left ⟶ A.left)) (ε : K → ℤ) (u : LB.Gen (LB.LinComb L.L φ ε)),
    u.IsGen ∧ (∀ (U : Type) [CommGroup U] (h : ((T ⊗ A).left ⟶ A.left) → U), ∏ i, h (φ i) ^ ε i =
      h (snd T A).left ^ k * (h ((fst T A ≫ x) * snd T A).left ^ k)⁻¹) ∧ ∀ y, val u (lift σ y).left z J = g.f y

variable {σ z J} (hJ : Good L.L z J) {k : ℕ} {x x' : T ⟶ A} {g g' : Th (T' ⟶ A) (T'.left.presheaf.stalk z)ˣ}
include hJ

theorem IsGeo.cub (c : CubicalStr A L) (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (h : IsGeo σ z J k x g) (hx : x ^ k = 1) (y) :
    g.f y = g.f 1 * cubN (cubV c z J) k 1 g.x y := by
  obtain ⟨e, K, _, φ, ε, u, hu, hF, v⟩ := h
  rw [← v, ← v, e]; exact val_theta c hG hA hx u hu hF σ y hJ

theorem IsGeo.mul (h : IsGeo σ z J k x g) (h' : IsGeo σ z J k x' g') : IsGeo σ z J k (x * x') (g * g') := by
  obtain ⟨e, K, _, φ, ε, u, hu, hF, v⟩ := h
  obtain ⟨e', K', _, φ', ε', u', hu', hF', v'⟩ := h'
  refine ⟨by rw [Th.adapted_frame_mul_vecMulVec, e, e', MonObj.comp_mul], _, inferInstance, _, _,
    LB.mulGen L.L _ _ _ _ u (LB.pullGen L.L _ _ u' (translT A x).left),
    mulGen_isGen _ _ _ _ _ _ _ hu (pullGen_isGen _ _ _ _ hu' _), fun U _ h => ?_, fun y => ?_⟩
  · refine (prod_sum₂ (K := K) (K' := K') (U := U) _ (hF U h) (hF' U fun q => h ((translT A x).left ≫ q))).trans ?_
    have a : translT A x ≫ snd T A = (fst T A ≫ x) * snd T A := lift_snd _ _
    have b : translT A x ≫ fst T A = fst T A := lift_fst _ _
    simp only [← Over.comp_left, MonObj.comp_mul, ← Category.assoc, a, b]
    rw [mul_left_comm (fst T A ≫ x'), ← _root_.mul_assoc (fst T A ≫ x), _root_.mul_assoc, inv_mul_cancel_left]
  · rw [val_mul hJ, val_pull hJ, ← Over.comp_left, lift_transl, v, v', Th.mul_f, e, mul_comm y]

theorem IsGeo.pull {a : ℕ} (f : A ⟶ A) [IsMonHom f] (h : IsGeo σ z J a (x ≫ f) g) {K₀ : Type} [Fintype K₀]
    {φ₀ : K₀ → (A.left ⟶ A.left)} {ε₀ : K₀ → ℤ} (δ : LB.Gen (LB.LinComb L.L φ₀ ε₀)) (hδ : δ.IsGen)
    (hF₀ : ∀ {T : Over S} (y : T ⟶ A) (U : Type) [CommGroup U] (h : (T.left ⟶ A.left) → U), ∏ i, h (y.left ≫ φ₀ i) ^ ε₀ i =
      h y.left ^ k * (h (y ≫ f).left ^ a)⁻¹) :
    IsGeo σ z J k x (g.pull (MonoidHom.mk' (· ≫ f) fun p q => MonObj.mul_comp p q f) (fun y => val δ y.left z J) (σ ≫ x)) := by
  obtain ⟨e, K, _, φ, ε, u, hu, hF, v⟩ := h
  let n : T ⊗ A ⟶ T ⊗ A := lift (fst T A) (snd T A ≫ f)
  refine ⟨rfl, _, inferInstance, _, _, LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ δ (snd T A).left)
    (LB.pullGen L.L _ _ u n.left)) (LB.invGen L.L _ _ (LB.pullGen L.L _ _ δ ((fst T A ≫ x) * snd T A).left)),
    mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hδ _) (pullGen_isGen _ _ _ _ hu _))
      (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hδ _)), fun U _ h => ?_, fun y => ?_⟩
  · refine (prod_sum₂ (K := K₀ ⊕ K) (K' := K₀) (U := U) _ (prod_sum₂ (K := K₀) (K' := K) (U := U) _ (hF₀ _ U h)
      (hF U fun q => h (n.left ≫ q))) (prod_neg _ _ (hF₀ _ U h))).trans ?_
    simp only [← Over.comp_left, MonObj.comp_mul, MonObj.mul_comp, n, lift_snd, lift_fst_assoc, Category.assoc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · rw [val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left,
      ← Over.comp_left, lift_snd, MonObj.comp_mul, lift_fst_assoc, lift_snd, comp_lift, lift_fst, lift_snd_assoc, v, mul_comm (σ ≫ x)]
    rfl

omit hJ in
theorem isGeo_one : IsGeo (L := L) σ z J k 1 1 :=
  ⟨(MonObj.comp_one σ).symm, PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, LB.oneGen L.L, fun i j => (map_one _).trans
    ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm, fun U _ h => by
      rw [MonObj.comp_one, _root_.one_mul]; simp, fun _ => val_one _⟩

theorem nu_pull (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {K₁ : Type} [Fintype K₁] {φ₁ : K₁ → (A.left ⟶ A.left)} {ε₁ : K₁ → ℤ}
    (ν : LB.Gen (LB.LinComb L.L φ₁ ε₁)) (hν : ν.IsGen)
    (hF₁ : ∀ {T : Over S} (y : T ⟶ A) (U : Type) [CommGroup U] (h : (T.left ⟶ A.left) → U), ∏ i, h (y.left ≫ φ₁ i) ^ ε₁ i =
      h y.left * (h y⁻¹.left)⁻¹) {a : ℕ} (f : A ⟶ A) [IsMonHom f] {K₀ : Type} [Fintype K₀]
    {φ₀ : K₀ → (A.left ⟶ A.left)} {ε₀ : K₀ → ℤ} (δ : LB.Gen (LB.LinComb L.L φ₀ ε₀)) (hδ : δ.IsGen)
    (hF₀ : ∀ {T : Over S} (y : T ⟶ A) (U : Type) [CommGroup U] (h : (T.left ⟶ A.left) → U), ∏ i, h (y.left ≫ φ₀ i) ^ ε₀ i =
      h y.left ^ k * (h (y ≫ f).left ^ a)⁻¹) : ∃ κ, ∀ y : T' ⟶ A, val ν y.left z J ^ k =
      κ * (val δ y.left z J * (val δ y⁻¹.left z J)⁻¹ * val ν (y ≫ f).left z J ^ a) := by
  have pw : ∀ (n : ℕ) (y : T' ⊗ A ⟶ A) (U : Type) [CommGroup U] (h : ((T' ⊗ A).left ⟶ A.left) → U),
      ∏ i, h (y.left ≫ φ₁ i) ^ ((n : ℤ) * ε₁ i) = (h y.left * (h y⁻¹.left)⁻¹) ^ n := fun n y U _ h => by
    rw [← hF₁ y U h, ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i _ => by rw [mul_comm, zpow_mul, zpow_natCast]
  let P : ∀ (n : ℕ) (y : T' ⊗ A ⟶ A), LB.Gen (LB.LinComb L.L (fun i => y.left ≫ φ₁ i) fun i => (n : ℤ) * ε₁ i) :=
    fun n y => ⟨fun j => (LB.pullGen L.L _ _ ν y.left).s j ^ n⟩
  have vP : ∀ n y (r : T'.left ⟶ _), val (P n y) r z J = val ν (r ≫ y.left) z J ^ n := fun n y r =>
    (map_pow _ _ _).trans (congrArg (· ^ n) (val_pull hJ ν y.left r))
  have gP : ∀ n y, (P n y).IsGen := fun n y => isGen_of_gm _ fun w j j' h h' => (map_pow _ _ _).trans
    ((congrArg (· ^ n) (gen_trans (pullGen_isGen _ _ _ _ hν y.left) (𝟙 _) w h h')).trans ((mul_pow _ _ _).trans
      (congrArg₂ (· * ·) (by
        rw [trF, trF, ← Finset.prod_pow]
        exact Finset.prod_congr rfl fun i _ => by rw [mul_comm, zpow_mul, zpow_natCast]) (map_pow _ _ _).symm)))
  have key := fun y => ratio_const hG hA L.isLB (fun U _ h => by
      refine (prod_sum₂ (K := K₀ ⊕ K₀) (K' := K₁) (U := U) _ (prod_sum₂ (K := K₀) (K' := K₀) (U := U) _ (hF₀ (snd T' A) U h)
        (prod_neg _ _ (hF₀ (snd T' A)⁻¹ U h))) (pw a (snd T' A ≫ f) U h)).trans (Eq.trans ?_ (pw k (snd T' A) U h).symm)
      rw [GrpObj.inv_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow]
      module) (gP k (snd T' A)) (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hδ (snd T' A).left)
        (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hδ (snd T' A)⁻¹.left))) (gP a (snd T' A ≫ f))) (𝟙 T') y hJ
  exact ⟨_, fun y => ((vP k _ _).trans (by rw [← Over.comp_left, lift_snd])).symm.trans ((eq_mul_inv_of_mul_eq (key y)).trans
    ((_root_.mul_assoc _ _ _).trans ((mul_comm _ _).trans (congrArg₂ (· * ·) rfl (by
      rw [val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, vP, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left,
        lift_snd, GrpObj.comp_inv, lift_snd, lift_snd_assoc])))))⟩

theorem symLift_geo (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {K₁ : Type} [Fintype K₁] {φ₁ : K₁ → (A.left ⟶ A.left)}
    {ε₁ : K₁ → ℤ} (ν : LB.Gen (LB.LinComb L.L φ₁ ε₁)) (hν : ν.IsGen)
    (hF₁ : ∀ {T : Over S} (y : T ⟶ A) (U : Type) [CommGroup U] (h : (T.left ⟶ A.left) → U), ∏ i, h (y.left ≫ φ₁ i) ^ ε₁ i =
      h y.left * (h y⁻¹.left)⁻¹) {kz : ℤ} (hk : kz = k) {n : ℕ} {W : ThetaGrp A L.L kz T} (h : SymLift A L.L kz n x W)
    (hn : x ^ n = 1) : IsGeo σ z J k x ⟨σ ≫ x, fun y => val (L := L.L) (φ := ![(snd T A).left, (translPt A W.pt).left])
      (ε := ![kz, -kz]) W.φ (lift σ y).left z J⟩ ∧ Th.Sym (fun y => val ν y.left z J ^ k) n ⟨σ ≫ x, fun y =>
      val (L := L.L) (φ := ![(snd T A).left, (translPt A W.pt).left]) (ε := ![kz, -kz]) W.φ (lift σ y).left z J⟩ := by
  subst hk
  obtain rfl := h.pt_eq
  refine ⟨⟨rfl, Fin 2, inferInstance, _, _, W.φ, W.isGen, fun U _ h => ?_, fun _ => rfl⟩, Th.ext ?_ (funext fun y => ?_), fun y => ?_⟩
  · rw [Fin.prod_univ_two]
    show h _ ^ (k : ℤ) * h _ ^ (-(k : ℤ)) = _
    rw [zpow_neg, zpow_natCast, zpow_natCast]; rfl
  · exact (Th.theta_pow_x _ _).trans ((MonObj.comp_pow _ _ _).symm.trans (by rw [hn, MonObj.comp_one]; rfl))
  · have e := (val_corr hJ h.pow_eq (lift σ y).left).trans (val_one _)
    have hz := hJ.mem (powφ A W.pt n) (lift σ y).left
    rw [Th.pow_f, ← Fin.prod_univ_eq_prod_range (fun j => val (L := L.L) (φ := ![(snd T A).left, (translPt A W.pt).left])
      (ε := ![(k : ℤ), -(k : ℤ)]) W.φ (lift σ (y * (σ ≫ W.pt) ^ j)).left z J)]
    refine Eq.trans (Finset.prod_congr rfl fun j _ => ?_) ((map_prod _ _ _).symm.trans e)
    refine Eq.trans ?_ ((gm_res _ z _ hz _).trans (val_pull hJ W.φ (translT A (W.pt ^ (j : ℕ))).left (lift σ y).left)).symm
    rw [← Over.comp_left, lift_transl, mul_comm, MonObj.comp_pow]
  · obtain ⟨mu, hmu, hs⟩ := h.sym
    have e := (val_corr hJ hs (lift σ y).left).trans (val_one _)
    have t₁ : (lift σ y).left ≫ (translT A W.pt⁻¹).left = (lift σ (y * (σ ≫ W.pt)⁻¹)).left := by
      rw [← Over.comp_left, lift_transl, mul_comm, GrpObj.comp_inv]
    have t₂ : (lift σ y).left ≫ (negT A T).left = (lift σ y⁻¹).left := by
      rw [← Over.comp_left, negT, comp_lift, lift_fst, lift_snd_assoc]; rfl
    have e' := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_pull hJ _ _ _).trans (congrArg (val _ · z J) t₁)) rfl)) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_pull hJ _ _ _).trans (congrArg (val _ · z J) t₂)) ((val_inv _ _).trans (congrArg (·⁻¹)
      ((val_pull hJ _ _ _).trans (congrArg (val _ · z J) t₁)))))))).symm.trans e
    let P : LB.Gen (LB.LinComb L.L (fun i => (snd T A).left ≫ φ₁ i) fun i => (k : ℤ) * ε₁ i) :=
      ⟨fun j => (LB.pullGen L.L _ _ ν (snd T A).left).s j ^ k⟩
    have vP : ∀ y : T' ⟶ A, val P (lift σ y).left z J = val ν y.left z J ^ k := fun y =>
      (map_pow _ _ _).trans (congrArg (· ^ k) ((val_pull hJ ν _ _).trans (by rw [← Over.comp_left, lift_snd])))
    have gP : P.IsGen := isGen_of_gm _ fun w j j' h h' => (map_pow _ _ _).trans
      ((congrArg (· ^ k) (gen_trans (pullGen_isGen _ _ _ _ hν _) (𝟙 _) w h h')).trans ((mul_pow _ _ _).trans
        (congrArg₂ (· * ·) (by
          rw [trF, trF, ← Finset.prod_pow]
          exact Finset.prod_congr rfl fun i _ => by rw [mul_comm, zpow_mul, zpow_natCast]) (map_pow _ _ _).symm)))
    have r := fun y => ratio_const hG hA L.isLB (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left])
      (ε := ![(k : ℤ), -(k : ℤ)]) (fun U _ h => by
        have := hF₁ (snd T A) U h
        rw [Fin.prod_univ_two]
        refine (Finset.prod_congr rfl fun i _ => by rw [mul_comm, zpow_mul, zpow_natCast]).trans
          ((Finset.prod_pow _ _ _).trans ?_)
        rw [this, mul_pow, inv_pow]
        show _ = h _ ^ (k : ℤ) * h _ ^ (-(k : ℤ))
        rw [zpow_neg, zpow_natCast, zpow_natCast]; rfl) hmu gP σ y hJ
    have r₁ := congrArg Additive.ofMul (r y)
    have r₂ := congrArg Additive.ofMul (r (y * (σ ≫ W.pt)⁻¹))
    have r₃ := congrArg Additive.ofMul e'
    apply Additive.ofMul.injective
    simp only [vP, ofMul_mul, ofMul_inv, ofMul_one] at r₁ r₂ r₃ ⊢
    linear_combination (norm := abel) r₃ - r₁ + r₂

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem twist_of_val {T : Over S} {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a b : ℤ} {M : LB A.left}
    (hM : M.IsLB) {α : LB.Gen (LB.LinComb M (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])} (hα : α.IsGen)
    {s : LB.Sec (LPow A M b T)} {s' : LB.Sec (LPow A M a T)} (h : ∀ z J, Good M z J →
      sval (L := M) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (𝟙 _) z J =
      (val α (𝟙 _) z J).val * sval (L := M) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (𝟙 _ ≫ ψ.left) z J) :
    IsTwistPull A M ψ m hm a b α s s' := fun j => fn_ext fun z hz => by
  choose J hJ using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hM (χ z)
  have hz' : (𝟙 (T ⊗ A).left : _ ⟶ _) z ∈ LB.wchart M ![(snd T A).left, m.left] j := hz
  have a₁ := (gs_res (𝟙 _) z (chart_le_zero A M m j) hz' (s'.f fun _ => j 0)).trans
    (sec_trans (L := M) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (𝟙 _) z (chart_le_zero A M m j hz')
      (Good.mem hJ _ _))
  have a₂ := ((gs_res (𝟙 _) z (chart_le_pull A M ψ m hm j) hz' ((ψ.left.app _).hom (s.f fun _ => j 1))).trans
    (gs_pull (𝟙 _) ψ.left z (LB.wchart M (fun _ : Fin 1 => (snd T A).left) fun _ => j 1) (chart_le_pull A M ψ m hm j hz') _)).trans
    (sec_trans (L := M) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => b) s (𝟙 _ ≫ ψ.left) z
      (chart_le_pull A M ψ m hm j hz') (Good.mem hJ _ _))
  have a₃ := (gs_unit (𝟙 _) z _ hz' (α.s j)).trans (congrArg Units.val (gen_trans hα (𝟙 _) z hz' (Good.mem hJ _ _)))
  refine a₁.trans (Eq.trans ?_ ((gs_mul (𝟙 _) z _ hz' _ _).trans (congrArg₂ (· * ·) a₃ a₂)).symm)
  refine (congrArg (_ * ·) (h z J hJ)).trans ?_
  have e : (𝟙 _ ≫ ψ.left) ≫ (snd T A).left = 𝟙 _ ≫ m.left := by rw [Category.assoc, ← Over.comp_left, hm]
  have t : trF (L := M) (K := Fin 2) ![(snd T A).left, m.left] ![a, -b] (𝟙 _) z j
        (fun k => J (𝟙 _ ≫ (![(snd T A).left, m.left] : Fin 2 → _) k)) *
      trF (L := M) (fun _ : Fin 1 => (snd T A).left) (fun _ => b) (𝟙 _ ≫ ψ.left) z (fun _ => j 1)
        (fun _ => J ((𝟙 _ ≫ ψ.left) ≫ (snd T A).left)) =
      trF (L := M) (fun _ : Fin 1 => (snd T A).left) (fun _ => a) (𝟙 _) z (fun _ => j 0) (fun _ => J (𝟙 _ ≫ (snd T A).left)) := by
    rw [trF, trF, trF, Fin.prod_univ_two, Fin.prod_univ_one, Fin.prod_univ_one, e]
    exact (_root_.mul_assoc _ _ _).trans ((congrArg (_ * ·) ((congrArg (· * _) (zpow_neg _ _)).trans (inv_mul_cancel _))).trans
      (_root_.mul_one _))
  rw [← t, Units.val_mul, Units.val_mul, _root_.mul_mul_mul_comm]
  rfl

variable [IsCommMonObj A] {L : RigLB A}

theorem isMonHom_mulA (n : ℕ) : IsMonHom (mulA A n) where
  one_hom := by
    have e : η[A] = (1 : 𝟙_ (Over S) ⟶ A) := by simp [Hom.one_def]
    rw [mulA, MonObj.comp_pow, Category.comp_id, e, one_pow]
  mul_hom := by
    have e : μ[A] = fst A A * snd A A := by simp [Hom.mul_def]
    rw [mulA, MonObj.comp_pow, Category.comp_id]
    conv_lhs => rw [e, mul_pow]
    rw [e, MonObj.comp_mul, tensorHom_fst, tensorHom_snd, MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, Category.comp_id]

def EndPull (L : RigLB A) (φ : A ⟶ A) (a b : ℤ) {T : Over S} (s : LB.Sec (LPow A L.L b T)) (s' : LB.Sec (LPow A L.L a T)) : Prop :=
  ∃ (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![a, -b]))
    (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T A).left, (snd T A ≫ φ).left] ![a, -b])),
    α₀.IsGen ∧ LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ α₀ (eSec A))
      (LB.mulGen L.L _ _ _ _ (rigPow A L.L L.rig a) (rigPow A L.L L.rig (-b))) ∧
    LB.Gen.Corr L.L _ _ _ _ α (LB.pullGen L.L _ _ α₀ (snd T A).left) ∧
    IsTwistPull A L.L (lift (fst T A) (snd T A ≫ φ)) (snd T A ≫ φ) (lift_snd _ _) a b α s s'

def MixedOver (L : RigLB A) (φ : A ⟶ A) (n k : ℕ) {T : Over S} (ok : (T ⟶ A) → Prop) (s : LB.Sec (LPow A L.L 1 T))
    (t₁ b : T ⟶ A) (hh : LB.Sec (LPow A L.L (k : ℤ) T)) : Prop :=
  ∃ (F₁ : LB.Sec (LPow A L.L ((n : ℤ) ^ 2) T))
    (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, φ.left] ![(k : ℤ), -((n : ℤ) ^ 2)]))
    (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T A).left, (snd T A ≫ φ).left] ![(k : ℤ), -((n : ℤ) ^ 2)]))
    (h₁ : LB.Sec (LPow A L.L (k : ℤ) T)) (U : ThetaGrp A L.L (k : ℤ) T),
    VtOver L n ok s t₁ F₁ ∧ α₀.IsGen ∧ LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ α₀ (eSec A))
      (LB.mulGen L.L _ _ _ _ (rigPow A L.L L.rig (k : ℤ)) (rigPow A L.L L.rig (-((n : ℤ) ^ 2)))) ∧
    LB.Gen.Corr L.L _ _ _ _ α (LB.pullGen L.L _ _ α₀ (snd T A).left) ∧
    IsTwistPull A L.L (lift (fst T A) (snd T A ≫ φ)) (snd T A ≫ φ) (lift_snd _ _) (k : ℤ) ((n : ℤ) ^ 2) α F₁ h₁ ∧
    SymLift A L.L (k : ℤ) k b U ∧ IsActOf A L.L (k : ℤ) U h₁ hh

omit [IsCommMonObj A] [GrpObj A] in
theorem prod_end (φ : A ⟶ A) {a b : ℕ} {a' b' : ℤ} (ha : a' = a) (hb : b' = b) {T : Over S} (y : T ⟶ A) (U : Type) [CommGroup U]
    (h : (T.left ⟶ A.left) → U) : ∏ i, h (y.left ≫ (![𝟙 A.left, φ.left] : Fin 2 → _) i) ^ (![a', -b'] : Fin 2 → ℤ) i =
      h y.left ^ a * (h (y ≫ φ).left ^ b)⁻¹ := by
  subst ha hb
  rw [Fin.prod_univ_two]
  simp [Over.comp_left, zpow_neg, zpow_natCast]

set_option maxHeartbeats 4000000 in
theorem mix_core (c : CubicalStr A L) (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hsym : L.IsSymmetric) {g n M : ℕ}
    (hM : M = g * n) (hN : Odd M) (p q f f' : A ⟶ A) [IsMonHom p] [IsMonHom q] [IsMonHom f] [IsMonHom f']
    (hpq : q ≫ p = mulA A g) (hqp : p ≫ q = mulA A g) (cp : p ≫ f' = f' ≫ p) (cq : q ≫ f' = f' ≫ q) (hr : RosatiAdj A L.L f f')
    {T : Over S} (ok : (T ⟶ A) → Prop) (hf : ∀ x, ok x → x ≫ f = 1) (hg : ∀ x, ok x → x ≫ f' = x)
    (hk : ∀ x, ok x → x ^ (M ^ 2) = 1) (hK : ∀ W : ThetaGrp A L.L ((n : ℤ) ^ 2) T, W.pt ^ (n ^ 2) = 1)
    {s : LB.Sec (LPow A L.L 1 T)} {t t₁ b : T ⟶ A} {F : LB.Sec (LPow A L.L ((M : ℤ) ^ 2) T)}
    {hh : LB.Sec (LPow A L.L ((g * n ^ 2 : ℕ) : ℤ) T)} (hb : ok b) (hbq : b ≫ q = 1) (ht : t = (b ≫ p) ^ n * t₁)
    (hF : VtOver L M ok s t F) (hH : MixedOver L p n (g * n ^ 2) ok s t₁ b hh) :
    EndPull L q ((M : ℤ) ^ 2) ((g * n ^ 2 : ℕ) : ℤ) hh F := by
  obtain ⟨_, β, βT, s₁, U, htU, oU, gβ, nβ, cβ, twβ, slU, acU⟩ := hF
  obtain ⟨F₁, α, αT, h₁, Ub, ⟨_, β', βT', s₁', U₁, ht₁, o₁, gβ', nβ', cβ', twβ', sl₁, ac₁⟩, gα, nα, cα, twα, slb, acb⟩ := hH
  obtain rfl := slU.pt_eq
  obtain rfl := sl₁.pt_eq
  obtain rfl := slb.pt_eq
  have := isMonHom_mulA (A := A) n
  have cM : ((M : ℤ) ^ 2) = ((M ^ 2 : ℕ) : ℤ) := by push_cast; rfl
  have cn : ((n : ℤ) ^ 2) = ((n ^ 2 : ℕ) : ℤ) := by push_cast; rfl
  have mul : ∀ {T : Over S} (y : T ⟶ A) (k : ℕ), y ≫ mulA A k = y ^ k := fun y k => by
    rw [mulA, MonObj.comp_pow, Category.comp_id]
  have yqp : ∀ {T : Over S} (y : T ⟶ A), ((y ≫ q) ≫ p) ^ n = y ^ M := fun y => by
    rw [Category.assoc, hpq, mul, ← pow_mul, hM]
  obtain ⟨ga, gga, vga⟩ := exists_gen L.isLB (φ' := ![𝟙 A.left, q.left]) (ε' := ![(M : ℤ) ^ 2, -((g * n ^ 2 : ℕ) : ℤ)])
    (fun V _ h => by
      have e₁ := prod_mulN M (𝟙 A) h
      have e₂ := prod_end q cM rfl (𝟙 A) V h (b := g * n ^ 2)
      simp only [Over.id_left, Category.id_comp] at e₁ e₂
      refine (prod_sum₂ (K := Fin 2) (K' := Fin 2 ⊕ Fin 2) (U := V) _ e₁ (prod_neg _ _ (prod_sum₂ (K := Fin 2) (K' := Fin 2)
        (U := V) _ (prod_end p rfl cn q V h) (prod_mulN n (q ≫ p) h)))).trans (Eq.trans ?_ e₂.symm)
      have := yqp (𝟙 A)
      rw [Category.id_comp] at this
      rw [this]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) (LB.mulGen L.L _ _ _ _ β (LB.invGen L.L _ _ (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ α q.left)
        (LB.pullGen L.L _ _ β' (q ≫ p).left))))
    (mulGen_isGen _ _ _ _ _ _ _ gβ (invGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ gα _)
      (pullGen_isGen _ _ _ _ gβ' _))))
  have vga' : ∀ {Z : Scheme.{0}} (r : Z ⟶ A.left) z J, Good L.L z J → val ga r z J =
      val β r z J * (val α (r ≫ q.left) z J * val β' (r ≫ (q ≫ p).left) z J)⁻¹ := fun r z J hJ => by
    rw [vga _ r z J hJ, val_mul hJ, val_inv, val_mul hJ, val_pull hJ, val_pull hJ]
  obtain ⟨gaT, ggaT, vgaT⟩ := exists_gen L.isLB (φ' := ![(snd T A).left, (snd T A ≫ q).left])
    (ε' := ![(M : ℤ) ^ 2, -((g * n ^ 2 : ℕ) : ℤ)]) (fun V _ h => Finset.prod_congr rfl fun i _ => by
      fin_cases i
      · exact congrArg (fun r => h r ^ _) (Category.comp_id _)
      · rfl) (LB.pullGen L.L _ _ ga (snd T A).left) (pullGen_isGen _ _ _ _ gga _)
  refine ⟨ga, gaT, gga, corr_of_val L.isLB fun w I hI => ?_, corr_of_val L.isLB fun w I hI => vgaT _ _ w I hI,
    twist_of_val L.isLB ggaT fun z J hJ => ?_⟩
  · have rp : ∀ k : ℤ, val (rigPow A L.L L.rig k) (𝟙 _) w I =
        val (L := L.L) (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) L.rig (𝟙 _) w I ^ k := fun k => map_zpow _ _ _
    have b₁ := (val_pull hI _ _ _).symm.trans ((val_corr hI nβ (𝟙 _)).trans ((val_mul hI _ _ _).trans
      (congrArg₂ (· * ·) (rp _) (val_inv _ _))))
    have b₂ := (val_pull hI _ _ _).symm.trans ((val_corr hI nβ' (𝟙 _)).trans ((val_mul hI _ _ _).trans
      (congrArg₂ (· * ·) (rp _) (val_inv _ _))))
    have b₃ := (val_pull hI _ _ _).symm.trans ((val_corr hI nα (𝟙 _)).trans ((val_mul hI _ _ _).trans
      (congrArg₂ (· * ·) (rp _) (rp _))))
    have e : ∀ (r : A ⟶ A) [IsMonHom r], (𝟙 _ ≫ eSec A) ≫ r.left = 𝟙 _ ≫ eSec A := fun r _ =>
      (Category.assoc _ _ _).trans (congrArg (fun x : 𝟙_ (Over S) ⟶ A => 𝟙 _ ≫ x.left) (IsMonHom.one_hom r))
    refine ((val_pull hI _ _ _).trans (vga' _ w I hI)).trans (Eq.trans ?_ ((val_mul hI _ _ _).trans
      (congrArg₂ (· * ·) (rp _) (rp _))).symm)
    rw [e q, e (q ≫ p), b₁, b₂, b₃]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    module
  have C : IsCub (cubV c (T := T ⊗ A) z J) := isCub_cubV c hJ
  obtain ⟨u, hu, nu⟩ := exists_ros hG hA L.isLB f f' hr
  obtain ⟨-, ws, gws, -⟩ := hsym
  obtain ⟨ν₀, hν₀⟩ := gen_of_iso ((isGen_iff ws).1 gws) (𝟙 A.left)
  have hν := invGen_isGen _ _ _ _ hν₀
  have Fν : ∀ {T : Over S} (y : T ⟶ A) (V : Type) [CommGroup V] (h : (T.left ⟶ A.left) → V),
      ∏ i, h (y.left ≫ (![𝟙 A.left ≫ (GrpObj.inv : A ⟶ A).left, 𝟙 A.left] : Fin 2 → _) i) ^ (-(![1, -1] : Fin 2 → ℤ) i) =
        h y.left * (h y⁻¹.left)⁻¹ := fun y V _ h => by
    rw [Fin.prod_univ_two]
    show h (y.left ≫ 𝟙 _ ≫ _) ^ (-1 : ℤ) * h (y.left ≫ 𝟙 _) ^ (- -1 : ℤ) = _
    rw [Category.id_comp, Category.comp_id, neg_neg, zpow_one, zpow_neg_one, mul_comm]; rfl
  let σ := fst T A
  have pk : ∀ {x : T ⟶ A} {k : ℕ}, x ^ k = 1 → (σ ≫ x) ^ k = 1 := fun h => by rw [← MonObj.comp_pow, h, MonObj.comp_one]
  have k₁ := hK U₁
  have kb : Ub.pt ^ (g * n ^ 2) = 1 := by
    rw [pow_mul, ← mul _ g, ← hpq, ← Category.assoc, hbq, MonObj.one_comp, one_pow]
  let v : T ⟶ A := Ub.pt⁻¹ * (U.pt ≫ q)
  let d : T ⟶ A := U₁.pt⁻¹ * (v ≫ p)
  have vp : (v ≫ p) ^ n = U₁.pt ^ n := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, mul_pow, inv_pow, yqp, htU, ht, inv_mul_cancel_left, ht₁]
  have dn : d ^ n = 1 := by rw [mul_pow, inv_pow, vp, inv_mul_cancel]
  have dn2 : d ^ (n ^ 2) = 1 := by rw [pow_two, pow_mul, dn, one_pow]
  have vk : v ^ (g * n ^ 2) = 1 := by
    rw [pow_mul, ← mul _ g, ← hqp, ← Category.assoc, ← MonObj.pow_comp, pow_two, pow_mul, vp, ← pow_mul, ← pow_two, k₁,
      MonObj.one_comp]
  have vg : v ≫ f' = v := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hg _ hb, Category.assoc, cq, ← Category.assoc, hg _ oU]
  have dg : d ≫ f' = d := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, hg _ o₁, Category.assoc, cp, ← Category.assoc, vg]
  have dv₁ : n ^ 2 ∣ M ^ 2 := pow_dvd_pow_of_dvd ⟨g, by rw [hM, mul_comm]⟩ 2
  have dv₂ : g * n ^ 2 ∣ M ^ 2 := ⟨g, by rw [hM]; ring⟩
  have pw : ∀ {x : T ⟶ A} {k : ℕ}, x ^ k = 1 → k ∣ M ^ 2 → (σ ≫ x) ^ (M ^ 2) = 1 := fun h ⟨r, hr⟩ => by
    rw [hr, pow_mul, pk h, one_pow]
  obtain ⟨G₁, S₁⟩ := symLift_geo (σ := σ) hJ hG hA _ hν Fν cn sl₁ k₁
  obtain ⟨Gb, Sb⟩ := symLift_geo (σ := σ) hJ hG hA _ hν Fν rfl slb kb
  obtain ⟨GU, SU⟩ := symLift_geo (σ := σ) hJ hG hA _ hν Fν cM slU (hk _ oU)
  have Fβ' : ∀ {T : Over S} (y : T ⟶ A) (V : Type) [CommGroup V] (h : (T.left ⟶ A.left) → V),
      ∏ i, h (y.left ≫ (![𝟙 A.left, (mulA A n).left] : Fin 2 → _) i) ^ (![(n : ℤ) ^ 2, -1] : Fin 2 → ℤ) i =
        h y.left ^ (n ^ 2) * (h (y ≫ mulA A n).left ^ 1)⁻¹ := fun y V _ h => by rw [prod_mulN, mul, pow_one]
  have Gd := IsGeo.pull hJ (σ := σ) (x := d) (mulA A n) (a := 1) (g := 1) (by rw [mul, dn]; exact isGeo_one) β' gβ' Fβ'
  obtain ⟨κ₁, hκ₁⟩ := nu_pull hJ hG hA _ hν Fν (mulA A n) β' gβ' Fβ'
  have Sd := (Th.sym_one (N := M ^ 2) (ν := fun y : T ⊗ A ⟶ A => val (LB.invGen L.L _ _ ν₀) y.left z J ^ 1)).pull (MonoidHom.mk' (· ≫ mulA A n) fun a b => MonObj.mul_comp a b _)
    (fun y => val β' y.left z J) (x := σ ≫ d) (by show (σ ≫ d) ≫ _ = 1; rw [mul, pk dn]) (pw dn2 dv₁) hκ₁
  have i₁ := ros_pow' c hG hA f f' u hu nu hJ (x := σ ≫ d) (m := σ ≫ U₁.pt) (pk dn2) (pk k₁)
    (by rw [Category.assoc, hf _ o₁, MonObj.comp_one])
  rw [Category.assoc, dg] at i₁
  have S₂ := (S₁.of_dvd dv₁).mul Sd (Th.commute_of C (pk k₁) (pk dn2) (G₁.cub hJ c hG hA k₁) (Gd.cub hJ c hG hA dn2) i₁)
  have G₂ := G₁.mul hJ Gd
  rw [show U₁.pt * d = v ≫ p from mul_inv_cancel_left _ _] at G₂
  have G₃ := G₂.pull hJ p α gα (prod_end p rfl cn)
  obtain ⟨κ₂, hκ₂⟩ := nu_pull hJ hG hA _ hν Fν p α gα (prod_end p rfl cn)
  have S₃ := S₂.pull (MonoidHom.mk' (· ≫ p) fun a b => MonObj.mul_comp a b _) (fun y => val α y.left z J) (x := σ ≫ v)
    ((Category.assoc _ _ _).trans G₂.1.symm) (pw vk dv₂) hκ₂
  have i₂ := ros_pow' c hG hA f f' u hu nu hJ (x := σ ≫ v) (m := σ ≫ Ub.pt) (pk vk) (pk kb)
    (by rw [Category.assoc, hf _ hb, MonObj.comp_one])
  rw [Category.assoc, vg] at i₂
  have S₄ := (Sb.of_dvd dv₂).mul S₃ (Th.commute_of C (pk kb) (pk vk) (Gb.cub hJ c hG hA kb) (G₃.cub hJ c hG hA vk) i₂)
  have G₄ := Gb.mul hJ G₃
  rw [show Ub.pt * v = U.pt ≫ q from mul_inv_cancel_left _ _] at G₄
  have G₅ := G₄.pull hJ q ga gga (prod_end q cM rfl)
  obtain ⟨κ₃, hκ₃⟩ := nu_pull hJ hG hA _ hν Fν q ga gga (prod_end q cM rfl)
  have S₅ := S₄.pull (MonoidHom.mk' (· ≫ q) fun a b => MonObj.mul_comp a b _) (fun y => val ga y.left z J) (x := σ ≫ U.pt)
    ((Category.assoc _ _ _).trans G₄.1.symm) (pk (hk _ oU)) hκ₃
  have E := SU.unique (hN.pow (n := 2)) S₅ rfl (fun y => (GU.cub hJ c hG hA (hk _ oU) y).trans
    (((congrArg₂ (· * ·) rfl (eq_inv_mul_of_mul_eq (G₅.cub hJ c hG hA (hk _ oU) y).symm)).trans (_root_.mul_assoc _ _ _).symm)))
  have E₁ := congrArg (fun x => x.f (snd T A)) E
  have i₀ : (lift σ (snd T A)).left = 𝟙 _ := congrArg (fun x => x.left) (lift_fst_snd : lift (fst T A) (snd T A) = 𝟙 _)
  have va : ∀ {m : T ⊗ A ⟶ A} {φ : A ⟶ A} {e : Fin 2 → ℤ} {β₀ : LB.Gen (LB.LinComb L.L ![𝟙 A.left, φ.left] e)}
      {β : LB.Gen (LB.LinComb L.L ![(snd T A).left, m.left] e)}
      (_ : LB.Gen.Corr L.L _ _ _ _ β (LB.pullGen L.L _ _ β₀ (snd T A).left)) (y : T ⊗ A ⟶ A),
      val β (lift σ y).left z J = val β₀ y.left z J := fun h y =>
    (val_corr hJ h _).trans ((val_pull hJ _ _ _).trans (by rw [← Over.comp_left, lift_snd]))
  have mt : ∀ (k : ℕ) (y : T ⊗ A ⟶ A), (lift σ y).left ≫ (mulT A T k).left = (lift σ (y ^ k)).left := fun k y => by
    rw [← Over.comp_left, mulT, comp_lift, lift_fst, MonObj.comp_pow, lift_snd]
  have et : ∀ (r : A ⟶ A) (y : T ⊗ A ⟶ A), (lift σ y).left ≫ (lift (fst T A) (snd T A ≫ r)).left = (lift σ (y ≫ r)).left :=
    fun r y => by rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc]
  have w₁ := twist_val acU (lift σ (snd T A)).left z hJ
  rw [← Over.comp_left, lift_transl, twist_val twβ _ z hJ, mt, va cβ] at w₁
  have w₂ := twist_val acb (lift σ (snd T A ≫ q)).left z hJ
  rw [← Over.comp_left, lift_transl, twist_val twα _ z hJ, et, va cα] at w₂
  have w₃ := twist_val ac₁ (lift σ (((σ ≫ Ub.pt) * (snd T A ≫ q)) ≫ p)).left z hJ
  rw [← Over.comp_left, lift_transl, twist_val twβ' _ z hJ, mt, va cβ'] at w₃
  have pt : ((σ ≫ U₁.pt) * ((σ ≫ Ub.pt) * (snd T A ≫ q)) ≫ p) ^ n = ((σ ≫ U.pt) * snd T A) ^ M := by
    have cpw : ∀ (x : T ⟶ A) (k : ℕ), (σ ≫ x) ^ k = σ ≫ x ^ k := fun x k => by rw [MonObj.comp_pow]
    rw [MonObj.mul_comp, mul_pow, mul_pow, mul_pow, yqp, Category.assoc, cpw, cpw, cpw, htU, ht, ht₁, MonObj.comp_mul,
      ← _root_.mul_assoc, mul_comm (σ ≫ t₁)]
  rw [w₃, pt] at w₂
  rw [← i₀, et, w₁, w₂, vgaT _ _ z J hJ, val_pull hJ, ← Over.comp_left, lift_snd]
  simp only [← _root_.mul_assoc, ← Units.val_mul]
  refine congrArg₂ (· * ·) (congrArg Units.val ?_) rfl
  have e₁ : (snd T A ≫ q) * (σ ≫ Ub.pt) * (σ ≫ v) = (snd T A * (σ ≫ U.pt)) ≫ q := by
    rw [_root_.mul_assoc, ← MonObj.comp_mul, mul_inv_cancel_left, MonObj.mul_comp, Category.assoc]
  have e₂ : ((snd T A ≫ q) * (σ ≫ Ub.pt)) ≫ p * (σ ≫ U₁.pt) * (σ ≫ d) = ((snd T A * (σ ≫ U.pt)) ≫ q) ≫ p := by
    rw [_root_.mul_assoc, ← MonObj.comp_mul, mul_inv_cancel_left, ← Category.assoc, ← MonObj.mul_comp, e₁]
  have g₁ := vga' (snd T A * (σ ≫ U.pt)).left z J hJ
  rw [← Over.comp_left, ← Over.comp_left, ← Category.assoc] at g₁
  simp only [Th.pull, Th.mul_f, MonoidHom.mk'_apply, e₁, e₂, g₁] at E₁
  rw [mul_comm (σ ≫ U.pt), mul_comm (σ ≫ U₁.pt), mul_comm (σ ≫ Ub.pt)]
  refine (congrArg (· * _) E₁).trans (Additive.ofMul.injective ?_)
  have o : ∀ y, (1 : Th (T ⊗ A ⟶ A) ((T ⊗ A).left.presheaf.stalk z)ˣ).f y = 1 := fun _ => rfl
  simp only [o, ofMul_mul, ofMul_inv, ofMul_one]
  abel

theorem theta_pt_pow (c : CubicalStr A L) (hK : KTriv A L.L) {R : Type} [CommRing R] (t : Sp R ⟶ S) {k : ℕ} {kz : ℤ}
    (hk : kz = k) (W : ThetaGrp A L.L kz (Over.mk t)) : W.pt ^ k = 1 := by
  subst hk
  refine hK R t _ fun p => ?_
  obtain ⟨V, hV, v, hv⟩ := exists_local_gen L.isLB (K := Fin 3) ![(W.pt ^ k).left, (1 : Over.mk t ⟶ A).left, W.pt.left]
    ![1, (k : ℤ) - 1, -(k : ℤ)] p
  obtain ⟨u, hu, -⟩ := exists_cubN c (1 : Over.mk t ⊗ A ⟶ A) (fst _ A ≫ W.pt) (snd _ A) k
  let i := ((fst (Over.mk t) A).left ⁻¹ᵁ V).ι
  obtain ⟨w, hw, -⟩ := exists_gen L.isLB (φ' := fun j => i ≫ (![((fst _ A ≫ W.pt ^ k) * snd _ A).left, (snd _ A).left] :
      Fin 2 → _) j) (ε' := ![1, -1]) (fun U _ h => by
      refine (prod_sum₂ (K := Fin 8 ⊕ Fin 2) (K' := Fin 3) (U := U) _ (prod_sum₂ (K := Fin 8) (K' := Fin 2) (U := U) _
        (Fin.prod_univ_eight _) (Fin.prod_univ_two _)) (Fin.prod_univ_three _)).trans ?_
      have e : ∀ q : Over.mk t ⟶ A, ((fst (Over.mk t) A).left ∣_ V) ≫ V.ι ≫ q.left = i ≫ (fst _ A ≫ q).left := fun q => by
        rw [← Category.assoc, morphismRestrict_ι, Category.assoc]; rfl
      rw [Fin.prod_univ_two]
      simp only [Sum.elim_inr, Sum.elim_inl, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, e, translPt_eq,
        _root_.one_mul, MonObj.comp_one, MonObj.comp_pow]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module) (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ u i)
        (LB.pullGen L.L _ _ (LB.invGen L.L _ _ (thG W)) i)) (LB.pullGen L.L _ _ v ((fst (Over.mk t) A).left ∣_ V)))
    (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hu _)
      (pullGen_isGen _ _ _ _ (invGen_isGen _ _ _ _ W.isGen) _)) (pullGen_isGen _ _ _ _ hv _))
  exact ⟨V, hV, gen_chartPull (chartPullOut L.L _ _ _ _ fun _ => rfl) w hw⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

set_option maxHeartbeats 800000 in

theorem mix_obj (hG : GlobalFnsSt) {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b₀ : Base l B} {s₀ : S ⟶ Sp B}
    (o : Obj D l b₀ s₀) {R : Type} [CommRing R] {x₀ : Sp R ⟶ S} {π : 𝓞 E} {g n : ℕ} (hπ : π * H.bar π = g) (hM : l.M = g * n)
    (hle : l.Mb ≤ Ideal.span {H.bar π}) {s : LB.Sec (LPow o.t.G o.t.PP.L 1 (Over.mk x₀))} {t t₁ b : Over.mk x₀ ⟶ o.t.G}
    {F : LB.Sec (LPow o.t.G o.t.PP.L ((l.M : ℤ) ^ 2) (Over.mk x₀))}
    {hh : LB.Sec (LPow o.t.G o.t.PP.L ((g * n ^ 2 : ℕ) : ℤ) (Over.mk x₀))}
    (hb : ∀ a ∈ Ideal.span {H.bar π}, b ≫ o.t.act.act a = 1) (ht : t = (b ≫ o.t.act.act π) ^ n * t₁)
    (hF : VtOver o.t.PP l.M (fun x => ∀ a ∈ l.Mb ^ 2, x ≫ o.t.act.act a = 1) s t F)
    (hH : MixedOver o.t.PP (o.t.act.act π) n (g * n ^ 2) (fun x => ∀ a ∈ l.Mb ^ 2, x ≫ o.t.act.act a = 1) s t₁ b hh) :
    EndPull o.t.PP (o.t.act.act (H.bar π)) ((l.M : ℤ) ^ 2) ((g * n ^ 2 : ℕ) : ℤ) hh F := by
  haveI := o.t.comm
  have hbb : ∀ a : 𝓞 E, H.bar (H.bar a) = a := fun a => by
    apply RingOfIntegers.ext
    show ((H.bar (H.bar a) : 𝓞 E) : E) = (a : E)
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
  have h0 : o.t.act.act 0 = 1 := by simpa using o.t.act.add 0 0
  have hnat : ∀ k : ℕ, o.t.act.act (k : 𝓞 E) = mulA o.t.G k := by
    intro k
    induction k with
    | zero => simp only [Nat.cast_zero, h0, mulA, pow_zero]
    | succ k ih =>
      simp only [mulA] at ih ⊢
      rw [Nat.cast_succ, o.t.act.add, ih, o.t.act.one, pow_succ]
  have hA : IsAbelianScheme o.t.G := by
    have hp := o.proper
    obtain ⟨⟩ := o.t.semi
    constructor <;> assumption
  have htop : l.Mb ^ 2 ⊔ (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2 = ⊤ :=
    Ideal.pow_sup_pow_eq_top l.coprime
  have h1mem : (1 : 𝓞 E) ∈ l.Mb ^ 2 ⊔ (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2 := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨e, he, w, hw, hew⟩ := Submodule.mem_sup.mp h1mem
  have hw' : w ∈ (l.Mb ^ 2).map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [Ideal.map_pow]; exact hw
  obtain ⟨y, hy, hyw⟩ := (Ideal.mem_map_iff_of_surjective _ H.bar.surjective).mp hw'
  have hbw : H.bar w ∈ l.Mb ^ 2 := by
    rw [← hyw]
    show H.bar (H.bar y) ∈ _
    rw [hbb]; exact hy
  have hMb : (l.M : 𝓞 E) ∈ l.Mb := by
    have hm : (l.M : 𝓞 E) ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.prod]; exact Ideal.mem_span_singleton_self _
    exact (Ideal.mul_le_inf.trans inf_le_left) hm
  haveI := o.t.act.hom π
  haveI := o.t.act.hom (H.bar π)
  haveI := o.t.act.hom e
  haveI := o.t.act.hom (H.bar e)
  refine mix_core o.t.cub hG hA o.t.sym hM l.odd (o.t.act.act π) (o.t.act.act (H.bar π))
    (o.t.act.act e) (o.t.act.act (H.bar e)) ?_ ?_ ?_ ?_ (o.t.rosatiAdj e)
    (fun x => ∀ a ∈ l.Mb ^ 2, x ≫ o.t.act.act a = 1) ?_ ?_ ?_ ?_ ?_ ?_ ht hF hH
  · rw [← o.t.act.mul, mul_comm, hπ, hnat]
  · rw [← o.t.act.mul, hπ, hnat]
  · rw [← o.t.act.mul, ← o.t.act.mul, mul_comm]
  · rw [← o.t.act.mul, ← o.t.act.mul, mul_comm]
  · exact fun x hx => hx e he
  · intro x hx
    have h1 : o.t.act.act (H.bar e) * o.t.act.act (H.bar w) = 𝟙 _ := by
      rw [← o.t.act.add, ← map_add, hew, map_one, o.t.act.one]
    have h2 := congrArg (fun u => x ≫ u) h1
    simp only [comp_mul, hx _ hbw, _root_.mul_one, Category.comp_id] at h2
    exact h2
  · intro x hx
    have h3 := hx ((l.M ^ 2 : ℕ) : 𝓞 E) (by rw [Nat.cast_pow]; exact Ideal.pow_mem_pow hMb 2)
    rwa [hnat, mulA, comp_pow, Category.comp_id] at h3
  · exact fun W => theta_pt_pow o.t.cub o.ktriv x₀ (k := n ^ 2) (by simp) W
  · exact fun a ha => hb a (hle (Ideal.pow_le_self two_ne_zero ha))
  · exact hb _ (Ideal.mem_span_singleton_self _)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end
