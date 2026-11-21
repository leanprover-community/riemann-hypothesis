import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.TopProdD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeibnizOrderOfExactSequences
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothIterPhi
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Prod.Pos

set_option linter.unusedSectionVars false

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dpow_sc (m : ℕ) (s : ℝ) (x : kˣ) :
    ((dpow m s (sc m x) : ℂˣ) : ℂ) = ((nabs k x ^ ((m : ℝ) * s) : ℝ) : ℂ) := by
  have hd : Matrix.GeneralLinearGroup.det (sc m x) = x ^ m := by
    ext; simp [sc, Matrix.GeneralLinearGroup.scalar]
  have hn : nabs k (x ^ m) = nabs k x ^ m := by simp [nabs]
  rw [dpow, detChar_apply, val_absPow_ofReal, hd, hn, ← Real.rpow_natCast_mul (nabs_pos' k x).le]

theorem tw_eig {m : ℕ} (A : GRep k m) (s : ℝ) (x : kˣ) (v : A.V) :
    (A.tw s).ρ (sc m x) v = ((nabs k x ^ ((m : ℝ) * s) : ℝ) : ℂ) • A.ρ (sc m x) v := by
  show ((dpow m s (sc m x) : ℂˣ) : ℂ) • A.ρ (sc m x) v = _
  rw [dpow_sc]

theorem untw {m : ℕ} (A : GRep k m) (s : ℝ) (x : kˣ) (c : ℂ) (v : A.V) (h : (A.tw s).ρ (sc m x) v = c • v) :
    A.ρ (sc m x) v = (c * ((nabs k x ^ (-((m : ℝ) * s)) : ℝ) : ℂ)) • v := by
  rw [tw_eig] at h
  calc A.ρ (sc m x) v = ((nabs k x ^ (-((m : ℝ) * s)) : ℝ) : ℂ) • ((nabs k x ^ ((m : ℝ) * s) : ℝ) : ℂ) •
        A.ρ (sc m x) v := by
        rw [smul_smul, ← Complex.ofReal_mul, ← Real.rpow_add (nabs_pos' k x), neg_add_cancel, Real.rpow_zero,
          Complex.ofReal_one, one_smul]
    _ = _ := by rw [h, smul_smul, mul_comm]

theorem retw {m : ℕ} (A : GRep k m) (s : ℝ) (x : kˣ) (c : ℂ) (v : A.V) (h : A.ρ (sc m x) v = c • v) :
    (A.tw s).ρ (sc m x) v = (((nabs k x ^ ((m : ℝ) * s) : ℝ) : ℂ) * c) • v := by
  rw [tw_eig, h, smul_smul]

theorem isSmooth_tw {m : ℕ} {A : GRep k m} (h : IsSmooth A.ρ) (s : ℝ) : IsSmooth (A.tw s).ρ :=
  isSmooth_twist h (IsSmoothChar.detChar (isSmoothChar_absPow (k := k) _))

theorem lfin_tw {m : ℕ} {A : GRep k m} (h : LFin A) (s : ℝ) : LFin (A.tw s) := by
  intro a
  obtain ⟨U, hU, ha, hst⟩ := h a
  refine ⟨U, hU, ha, fun x u hu => ?_⟩
  exact U.smul_mem ((dpow m s (sc m x) : ℂˣ) : ℂ) (hst x u hu)

theorem isSmooth_derivB (ψ : AddChar k Circle) : ∀ (j : ℕ) {n : ℕ} (π : GRep k (n + j)), IsSmooth π.ρ →
    IsSmooth (derivB ψ j π).ρ
  | 0, _, _, h => h
  | j + 1, _, _, h => GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_deriv ψ j h

theorem isAdm_cast {a b : ℕ} (h : a = b) {π : GRep k a} (hπ : IsAdmissible π.ρ) : IsAdmissible (π.cast h).ρ := by
  subst h; exact hπ

theorem irr_cast {a b : ℕ} (h : a = b) {π : GRep k a} (hπ : π.ρ.IsIrreducible) : (π.cast h).ρ.IsIrreducible := by
  subst h; exact hπ

theorem unit_cast {a b : ℕ} (h : a = b) {π : GRep k a} (hπ : IsUnitarisable π.ρ) : IsUnitarisable (π.cast h).ρ := by
  subst h; exact hπ

theorem cast_cast {a b c : ℕ} (h : a = b) (h' : b = c) (π : GRep k a) : (π.cast h).cast h' = π.cast (h.trans h') := by
  subst h; subst h'; rfl

theorem eig_cast {a b : ℕ} (h : a = b) (π : GRep k a) (x : kˣ) (c : ℂ) (v : (π.cast h).V) (hv0 : v ≠ 0)
    (hv : (π.cast h).ρ (sc b x) v = c • v) : ∃ w : π.V, w ≠ 0 ∧ π.ρ (sc a x) w = c • w := by
  subst h; exact ⟨v, hv0, hv⟩

theorem adm {n : ℕ} (π : GRep k n) (hs : IsSmooth π.ρ) (hi : π.ρ.IsIrreducible) : IsAdmissible π.ρ :=
  PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k n π.V π.ρ hs hi

theorem norm_eig_of_unit {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    (hu : IsUnitarisable ρ) {g : G} {c : ℂ} {v : V} (hv : v ≠ 0) (h : ρ g v = c • v) : ‖c‖ = 1 := by
  obtain ⟨B, -, hpos, hinv⟩ := hu
  have h1 := hinv g v v
  simp only [h, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul] at h1
  have hB : B v v ≠ 0 := fun h0 => by have := hpos v hv; rw [h0] at this; simp at this
  have h2 : c * (starRingEnd ℂ) c = 1 := by
    apply mul_right_cancel₀ hB
    linear_combination h1
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h2
  have h3 : ‖c‖ ^ 2 = 1 := by exact_mod_cast h2
  have h4 := norm_nonneg c
  nlinarith

theorem nontrivial_of_ne_bot {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    (W : Subrepresentation ρ) (hW : W ≠ ⊥) : Nontrivial W.toSubmodule := by
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  apply hW
  apply Subrepresentation.ext
  rw [Submodule.eq_bot_of_subsingleton (p := W.toSubmodule)]
  rfl

theorem subquot_sub {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    (W : Subrepresentation ρ) : IsSubquotient W.toRepresentation ρ :=
  ⟨W, Representation.IntertwiningMap.id _, Function.surjective_id⟩

theorem pipe (hL : GlobalTheory.RgGu.Leib.LeibnizOrd k) (hLF : LFDeriv k) (hE : EigProd k) (hF : EigFilt k)
    (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) {r t : ℕ} (π₁ : GRep k r) (π₂ : GRep k t)
    (hs₁ : IsSmooth π₁.ρ) (ha₁ : IsAdmissible π₁.ρ) (hs₂ : IsSmooth π₂.ρ) (ha₂ : IsAdmissible π₂.ρ)
    (ℓ n : ℕ) (e : r + t = n + ℓ) (x : kˣ) (c : ℂ) (v : (derivB ψ ℓ ((π₁.prod π₂).cast e)).V) (hv0 : v ≠ 0)
    (hv : (derivB ψ ℓ ((π₁.prod π₂).cast e)).ρ (sc n x) v = c • v) :
    ∃ (i : ℕ) (h : i ≤ r ∧ ℓ - i ≤ t) (cA cB : ℂ), i ≤ ℓ ∧ c = cA * cB ∧
      (∃ a : ((derivB ψ i (π₁.cast (Nat.sub_add_cancel h.1).symm)).tw (((ℓ - i : ℕ) : ℝ) / 2)).V, a ≠ 0 ∧
        ((derivB ψ i (π₁.cast (Nat.sub_add_cancel h.1).symm)).tw (((ℓ - i : ℕ) : ℝ) / 2)).ρ (sc (r - i) x) a =
          cA • a) ∧
      ∃ b : ((derivB ψ (ℓ - i) (π₂.cast (Nat.sub_add_cancel h.2).symm)).tw ((i : ℝ) / 2)).V, b ≠ 0 ∧
        ((derivB ψ (ℓ - i) (π₂.cast (Nat.sub_add_cancel h.2).symm)).tw ((i : ℝ) / 2)).ρ (sc (t - (ℓ - i)) x) b =
          cB • b := by
  obtain ⟨F, hanti, h0, hbot, hpieces⟩ := hL ψ hc h1 r t ℓ n e π₁ π₂ hs₁ hs₂
  obtain ⟨i, hi, w, hw0, hw⟩ := hF n _ (derivB ψ ℓ ((π₁.prod π₂).cast e)).ρ ℓ F hanti h0 hbot x c v hv0 hv
  have hp := hpieces i hi
  split_ifs at hp with h
  · obtain ⟨hsz, ⟨eq⟩⟩ := hp
    have hw' := GlobalTheory.CompanionTheory.LeibOrd.eint eq (sc n x) w
    rw [hw, map_smul] at hw'
    have hw0' : eq w ≠ 0 := fun h0' =>
      hw0 (eq.toLinearEquiv.injective ((show eq.toLinearEquiv w = 0 from h0').trans (map_zero _).symm))
    obtain ⟨f, hf0, hf⟩ := eig_cast hsz _ x c _ hw0' hw'.symm
    have hsA := isSmooth_tw (isSmooth_derivB ψ i _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast
      (Nat.sub_add_cancel h.1).symm hs₁)) (((ℓ - i : ℕ) : ℝ) / 2)
    have hsB := isSmooth_tw (isSmooth_derivB ψ (ℓ - i) _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast
      (Nat.sub_add_cancel h.2).symm hs₂)) ((i : ℝ) / 2)
    have hlA := lfin_tw (hLF ψ hc (r - i) i _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast (Nat.sub_add_cancel h.1).symm hs₁)
      (isAdm_cast (Nat.sub_add_cancel h.1).symm ha₁)) (((ℓ - i : ℕ) : ℝ) / 2)
    have hlB := lfin_tw (hLF ψ hc (t - (ℓ - i)) (ℓ - i) _
      (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast (Nat.sub_add_cancel h.2).symm hs₂)
      (isAdm_cast (Nat.sub_add_cancel h.2).symm ha₂)) ((i : ℝ) / 2)
    obtain ⟨cA, cB, hcc, ⟨a, ha0, hea⟩, b, hb0, heb⟩ := hE _ _ _ _ hsA hsB hlA hlB x c f hf0 hf
    exact ⟨i, h, cA, cB, hi, hcc, ⟨a, ha0, hea⟩, b, hb0, heb⟩
  · exfalso
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    apply hw0
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    show u.1 ∈ (F (i + 1)).toSubmodule
    rw [← hp]
    exact u.2

end PositivityTheory.RgUd.Prod.Pos
end
end

section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Prod.Pos

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem norm_untw (X : ℝ) (hX0 : 0 < X) (y : ℝ) (c : ℂ) : ‖c * ((X ^ (-y) : ℝ) : ℂ)‖ * X ^ y = ‖c‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hX0 _), mul_assoc,
    ← Real.rpow_add hX0, neg_add_cancel, Real.rpow_zero, mul_one]

theorem norm_combo (X : ℝ) (hX0 : 0 < X) (p y u : ℝ) (c : ℂ) (hsum : p + -y + u = 0) :
    ‖((X ^ p : ℝ) : ℂ) * (c * ((X ^ (-y) : ℝ) : ℂ))‖ * X ^ u = ‖c‖ := by
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hX0 _), abs_of_pos (Real.rpow_pos_of_pos hX0 _),
    show X ^ p * (‖c‖ * X ^ (-y)) * X ^ u = ‖c‖ * (X ^ p * X ^ (-y) * X ^ u) by ring,
    ← Real.rpow_add hX0, ← Real.rpow_add hX0, hsum, Real.rpow_zero, mul_one]

theorem fac_bound (hT : DerivTop k) (hP : DerivPos k) (hC : CentralSub k) (hLF : LFDeriv k)
    (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) {r : ℕ} (π : GRep k r) (hs : IsSmooth π.ρ)
    (hirr : π.ρ.IsIrreducible) (hu : IsUnitarisable π.ρ) (ha : IsAdmissible π.ρ) (i : ℕ) (hi : i ≤ r) (s : ℝ)
    (x : kˣ) (hx : nabs k x < 1) (cA : ℂ)
    (a : ((derivB ψ i (π.cast (Nat.sub_add_cancel hi).symm)).tw s).V) (ha0 : a ≠ 0)
    (hea : ((derivB ψ i (π.cast (Nat.sub_add_cancel hi).symm)).tw s).ρ (sc (r - i) x) a = cA • a) :
    ‖cA‖ ≤ nabs k x ^ (((r - i : ℕ) : ℝ) * (s + ((i : ℝ) - 1) / 2)) ∧
    (‖cA‖ = nabs k x ^ (((r - i : ℕ) : ℝ) * (s + ((i : ℝ) - 1) / 2)) →
      ∀ (n' h' : ℕ) (e : r = n' + h'), i < h' → Subsingleton (derivB ψ h' (π.cast e)).V) := by
  have hX0 : 0 < nabs k x := nabs_pos' k x
  have hd := untw (derivB ψ i (π.cast (Nat.sub_add_cancel hi).symm)) s x cA a hea
  have hm0 : (0 : ℝ) ≤ ((r - i : ℕ) : ℝ) := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos i with rfl | hi1
  · have hu' : IsUnitarisable (derivB ψ 0 (π.cast (Nat.sub_add_cancel hi).symm)).ρ :=
      unit_cast (Nat.sub_add_cancel hi).symm hu
    have h1' := norm_eig_of_unit hu' ha0 hd
    have hcA : ‖cA‖ = nabs k x ^ (((r - 0 : ℕ) : ℝ) * s) := by
      rw [← norm_untw _ hX0 (((r - 0 : ℕ) : ℝ) * s) cA, h1', one_mul]
    have hle : ((r - 0 : ℕ) : ℝ) * (s + (((0 : ℕ) : ℝ) - 1) / 2) ≤ ((r - 0 : ℕ) : ℝ) * s := by
      simp only [Nat.cast_zero]; nlinarith
    refine ⟨hcA ▸ Real.rpow_le_rpow_of_exponent_ge hX0 hx.le hle, fun heq n' h' e hlt => ?_⟩
    exfalso
    have hr : r = 0 := by
      by_contra hr
      have hmpos : (0 : ℝ) < ((r - 0 : ℕ) : ℝ) := Nat.cast_pos.2 (by omega)
      have hlt2 : ((r - 0 : ℕ) : ℝ) * (s + (((0 : ℕ) : ℝ) - 1) / 2) < ((r - 0 : ℕ) : ℝ) * s := by
        simp only [Nat.cast_zero]; nlinarith
      have := Real.rpow_lt_rpow_of_exponent_gt hX0 hx hlt2
      rw [← hcA, ← heq] at this
      exact lt_irrefl _ this
    omega
  · have hd' := retw (derivB ψ i (π.cast (Nat.sub_add_cancel hi).symm)) ((1 - (i : ℝ)) / 2) x _ a hd
    have key := norm_combo (nabs k x) hX0 (((r - i : ℕ) : ℝ) * ((1 - (i : ℝ)) / 2)) (((r - i : ℕ) : ℝ) * s)
      (((r - i : ℕ) : ℝ) * (s + ((i : ℝ) - 1) / 2)) cA (by ring)
    have hT0 : 0 < nabs k x ^ (((r - i : ℕ) : ℝ) * (s + ((i : ℝ) - 1) / 2)) := Real.rpow_pos_of_pos hX0 _
    by_cases htop : ∃ (n' h' : ℕ) (e : (r - i) + i = n' + h'), i < h' ∧
        Nontrivial (derivB ψ h' ((π.cast (Nat.sub_add_cancel hi).symm).cast e)).V
    · have hsD := isSmooth_tw (isSmooth_derivB ψ i _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast
        (Nat.sub_add_cancel hi).symm hs)) ((1 - (i : ℝ)) / 2)
      have hlD := lfin_tw (hLF ψ hc (r - i) i _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast (Nat.sub_add_cancel hi).symm hs)
        (isAdm_cast (Nat.sub_add_cancel hi).symm ha)) ((1 - (i : ℝ)) / 2)
      obtain ⟨W, ω, hW, hcc, hωx⟩ := hC (r - i) _ hsD hlD x _ a ha0 hd'
      have hlt := hP ψ hc h1 (r - i) i (π.cast (Nat.sub_add_cancel hi).symm) hi1
        (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast _ hs) (irr_cast _ hirr) (unit_cast _ hu) htop
        W.toSubmodule W.toRepresentation ω (nontrivial_of_ne_bot W hW) (subquot_sub W) hcc x hx
      rw [hωx] at hlt
      have hlt2 : ‖cA‖ < nabs k x ^ (((r - i : ℕ) : ℝ) * (s + ((i : ℝ) - 1) / 2)) := by
        rw [← key]
        nlinarith [norm_nonneg (((nabs k x ^ (((r - i : ℕ) : ℝ) * ((1 - (i : ℝ)) / 2)) : ℝ) : ℂ) *
          (cA * ((nabs k x ^ (-(((r - i : ℕ) : ℝ) * s)) : ℝ) : ℂ)))]
      exact ⟨hlt2.le, fun heq => absurd heq hlt2.ne⟩
    · have hnt : Nontrivial (derivB ψ i (π.cast (Nat.sub_add_cancel hi).symm)).V := ⟨⟨a, 0, ha0⟩⟩
      have htop' : ∀ (n' h' : ℕ) (e : (r - i) + i = n' + h'), i < h' →
          Subsingleton (derivB ψ h' ((π.cast (Nat.sub_add_cancel hi).symm).cast e)).V :=
        fun n' h' e hlt => not_nontrivial_iff_subsingleton.1 (fun hn => htop ⟨n', h', e, hlt, hn⟩)
      obtain ⟨-, hun⟩ := hT ψ hc h1 (r - i) i (π.cast (Nat.sub_add_cancel hi).symm) hi1
        (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast _ hs) (irr_cast _ hirr) (unit_cast _ hu) hnt htop'
      have h1' := norm_eig_of_unit hun ha0 hd'
      have heq : ‖cA‖ = nabs k x ^ (((r - i : ℕ) : ℝ) * (s + ((i : ℝ) - 1) / 2)) := by
        rw [← key, h1', one_mul]
      refine ⟨heq.le, fun _ n' h' e hlt => ?_⟩
      have := htop' n' h' ((Nat.sub_add_cancel hi).trans e) hlt
      rwa [cast_cast] at this

variable (k)

theorem posProd_of : DerivTop k → DerivPos k → GlobalTheory.RgGu.Leib.LeibnizOrd k → LFDeriv k → CentralSub k → EigProd k →
    EigFilt k → PosProdD k := by
  intro hT hP hL hLF hC hE hF ψ hc h1 r t π₁ π₂ hs₁ hi₁ hu₁ hs₂ hi₂ hu₂ n h e htop n' j e' hj x hx v c hv0 hv
  have ha₁ := adm π₁ hs₁ hi₁
  have ha₂ := adm π₂ hs₂ hi₂
  obtain ⟨i, hi, cA, cB, hil, rfl, ⟨a, ha0, hea⟩, b, hb0, heb⟩ :=
    pipe hL hLF hE hF ψ hc h1 π₁ π₂ hs₁ ha₁ hs₂ ha₂ j n' e' x c v hv0 hv
  obtain ⟨b1, t1⟩ := fac_bound hT hP hC hLF ψ hc h1 π₁ hs₁ hi₁ hu₁ ha₁ i hi.1 _ x hx cA a ha0 hea
  obtain ⟨b2, t2⟩ := fac_bound hT hP hC hLF ψ hc h1 π₂ hs₂ hi₂ hu₂ ha₂ (j - i) hi.2 _ x hx cB b hb0 heb
  have hX0 : 0 < nabs k x := nabs_pos' k x
  have hsz : (r - i) + (t - (j - i)) = n' := by omega
  have hexp : ((r - i : ℕ) : ℝ) * ((((j - i : ℕ) : ℝ) / 2) + ((i : ℝ) - 1) / 2) +
      ((t - (j - i) : ℕ) : ℝ) * (((i : ℝ) / 2) + (((j - i : ℕ) : ℝ) - 1) / 2) = (n' : ℝ) * ((j : ℝ) - 1) / 2 := by
    have h3 : ((r - i : ℕ) : ℝ) + ((t - (j - i) : ℕ) : ℝ) = (n' : ℝ) := by exact_mod_cast hsz
    have h4 : ((j - i : ℕ) : ℝ) = (j : ℝ) - (i : ℝ) := Nat.cast_sub hil
    rw [h4, ← h3]; ring
  rw [← hexp, Real.rpow_add hX0, norm_mul]
  have hB1 := Real.rpow_pos_of_pos hX0 (((r - i : ℕ) : ℝ) * ((((j - i : ℕ) : ℝ) / 2) + ((i : ℝ) - 1) / 2))
  have hB2 := Real.rpow_pos_of_pos hX0 (((t - (j - i) : ℕ) : ℝ) * (((i : ℝ) / 2) + (((j - i : ℕ) : ℝ) - 1) / 2))
  by_contra hge
  have eqA : ‖cA‖ = nabs k x ^ (((r - i : ℕ) : ℝ) * ((((j - i : ℕ) : ℝ) / 2) + ((i : ℝ) - 1) / 2)) := by
    by_contra hne
    exact hge (lt_of_le_of_lt (mul_le_mul_of_nonneg_left b2 (norm_nonneg _))
      (mul_lt_mul_of_pos_right (lt_of_le_of_ne b1 hne) hB2))
  have eqB : ‖cB‖ = nabs k x ^ (((t - (j - i) : ℕ) : ℝ) * (((i : ℝ) / 2) + (((j - i : ℕ) : ℝ) - 1) / 2)) := by
    by_contra hne
    exact hge (lt_of_le_of_lt (mul_le_mul_of_nonneg_right b1 (norm_nonneg _))
      (mul_lt_mul_of_pos_left (lt_of_le_of_ne b2 hne) hB1))
  have top1 := t1 eqA
  have top2 := t2 eqB
  obtain ⟨hnt, -⟩ := htop
  obtain ⟨v', hv'⟩ := @exists_ne _ hnt 0
  have hsc : sc n (1 : kˣ) = 1 := map_one _
  have hv1 : (derivB ψ h ((π₁.prod π₂).cast e)).ρ (sc n 1) v' = (1 : ℂ) • v' := by simp [hsc]
  obtain ⟨i', hi', -, -, hil', -, ⟨a', ha', -⟩, b', hb', -⟩ :=
    pipe hL hLF hE hF ψ hc h1 π₁ π₂ hs₁ ha₁ hs₂ ha₂ h n e 1 1 v' hv' hv1
  by_cases hcase : i < i'
  · exact ha' (@Subsingleton.elim _ (top1 (r - i') i' (Nat.sub_add_cancel hi'.1).symm hcase) a' 0)
  · exact hb' (@Subsingleton.elim _ (top2 (t - (h - i')) (h - i') (Nat.sub_add_cancel hi'.2).symm (by omega)) b' 0)

end PositivityTheory.RgUd.Prod.Pos
end
end
