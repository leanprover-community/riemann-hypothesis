import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClopenIsCompactQLat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaUnfoldingEquivariantUnitaryGroups
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLinearModelLatticeVacuumBaseStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatTensorIndicatorCharacterFacts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedCharacterDetLatticeStabilizerEqOne

section
section
open GlobalTheory.FinPl GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData ValuativeRel IsLocalRing Matrix
open GlobalTheory.LastSteps (exists_dual dual_ext finsum_split finsum_ofDual exists_lifts lifts_unique cosetInd_eq
  inDual_of_lifts term_ne_zero term_zero datum_eq lastPair_hasVal)

noncomputable section

namespace GlobalTheory.GluedExp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type}

theorem card_dual (L : Submodule 𝒪[k] (n → k)) [Fintype n] [L.IsLattice k] :
    Nat.card (Module.Dual 𝓀[k] (Red L)) = resCard k ^ Fintype.card n := by
  rw [Module.natCard_eq_pow_finrank (K := 𝓀[k]), Subspace.dual_finrank_eq, ← Module.natCard_eq_pow_finrank,
    Red.card_eq]

open Classical in

theorem finsum_char (χ : AddChar 𝓀[k] ℂ) (hχ : χ ≠ 1) (L : Submodule 𝒪[k] (n → k)) [Fintype n] [L.IsLattice k]
    (z : Red L) : ∑ᶠ f : Module.Dual 𝓀[k] (Red L), χ (-f z) =
      if z = 0 then ((resCard k : ℂ) ^ Fintype.card n) else 0 := by
  classical
  letI := Fintype.ofFinite (Module.Dual 𝓀[k] (Red L))
  rw [finsum_eq_sum_of_fintype]
  split_ifs with hz
  · subst hz
    simp only [map_zero, neg_zero, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one]
    rw [Fintype.card_eq_nat_card, card_dual]
    push_cast
    rfl
  · obtain ⟨f₁, hf₁⟩ : ∃ f₁ : Module.Dual 𝓀[k] (Red L), f₁ z ≠ 0 := by
      by_contra h
      push_neg at h
      exact hz ((Module.forall_dual_apply_eq_zero_iff 𝓀[k] z).1 h)
    obtain ⟨a, ha⟩ : ∃ a, χ a ≠ 1 := by
      by_contra h
      push_neg at h
      exact hχ (by ext a; rw [h a, AddChar.one_apply])
    set g : Module.Dual 𝓀[k] (Red L) := (-(a * (f₁ z)⁻¹)) • f₁
    have hg : g z = -a := by simp [g, hf₁]
    set S := ∑ f : Module.Dual 𝓀[k] (Red L), χ (-f z)
    have hS : S = χ a * S := by
      conv_lhs => rw [show S = ∑ f : Module.Dual 𝓀[k] (Red L), χ (-(f + g) z) from
        (Fintype.sum_equiv (Equiv.addRight g) _ _ fun _ => rfl).symm]
      simp only [LinearMap.add_apply, hg, neg_add, neg_neg, AddChar.map_add_eq_mul, S, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have : (1 - χ a) * S = 0 := by rw [sub_mul, one_mul, ← hS, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm ha))

end GlobalTheory.GluedExp

namespace GlobalTheory.GluedExp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type}
  [Fintype n] [Fintype n']

theorem card_ne_zero (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] : ((resCard k : ℂ) ^ Fintype.card n) ≠ 0 := by
  have h : Nat.card (Module.Dual 𝓀[k] (Red L)) ≠ 0 := Nat.card_pos.ne'
  rw [card_dual] at h
  exact_mod_cast h

omit [Fintype n] in

theorem withCol_split (x : Matrix n (n' ⊕ Fin 1) k) :
    withCol (x.submatrix id Sum.inl) (fun i => x i (Sum.inr 0)) = x := by
  ext i (j | j)
  · rfl
  · fin_cases j
    rfl

def imgE (q : Unif k) (P : Pair k n') {L : Submodule 𝒪[k] (n → k)} {x₀ : Matrix n n' k}
    (h0 : ∀ z ∈ P.ker, x₀ *ᵥ z ∈ L) : L :=
  ⟨x₀ *ᵥ (q.1 • P.vec), h0 _ (Pair.smul_mem_ker q.mem_max P.hasVal_vec.mem)⟩

theorem term_pos (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (P : Pair k n') {L : Submodule 𝒪[k] (n → k)}
    {x₀ : Matrix n n' k} (h0 : ∀ z ∈ P.ker, x₀ *ᵥ z ∈ L) (f : Module.Dual 𝓀[k] (Red L)) :
    term q χ 1 P L f x₀ = χ (-f (Red.mk L (imgE q P h0))) := by
  rw [term, dif_pos h0, Units.val_one, one_mul]
  rfl

theorem term_neg (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (P : Pair k n') {L : Submodule 𝒪[k] (n → k)}
    {x₀ : Matrix n n' k} (h0 : ¬ ∀ z ∈ P.ker, x₀ *ᵥ z ∈ L) (f : Module.Dual 𝓀[k] (Red L)) :
    term q χ 1 P L f x₀ = 0 := by
  rw [term, dif_neg h0]

open Classical in

theorem datum_expand (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (hχ : χ ≠ 1) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]
    (P : Pair k n') (x₀ : Matrix n n' k) (y : n → k) :
    datum q P L x₀ y = ((resCard k : ℂ) ^ Fintype.card n)⁻¹ *
      ∑ᶠ f : Module.Dual 𝓀[k] (Red L), term q χ 1 P L f x₀ *
        (if h : y ∈ L then χ (-f (Red.mk L ⟨y, h⟩)) else 0) := by
  classical
  by_cases h0 : ∀ z ∈ P.ker, x₀ *ᵥ z ∈ L
  · by_cases hy : y ∈ L
    · have key : ∀ f : Module.Dual 𝓀[k] (Red L), term q χ 1 P L f x₀ *
          (if h : y ∈ L then χ (-f (Red.mk L ⟨y, h⟩)) else 0) =
          χ (-f (Red.mk L (⟨y, hy⟩ + imgE q P h0))) := fun f => by
        rw [term_pos q χ P h0, dif_pos hy, map_add, map_add, neg_add, AddChar.map_add_eq_mul, mul_comm]
      rw [finsum_congr key, finsum_char χ hχ, Red.mk_eq_zero q]
      have hc : q.inv • ((⟨y, hy⟩ + imgE q P h0 : L) : n → k) = q.inv • y + x₀ *ᵥ P.vec := by
        simp only [imgE, Submodule.coe_add, smul_add, mulVec_smul, q.inv_smul_smul]
      rw [hc, datum]
      split_ifs with h1 h2 h2
      · exact (inv_mul_cancel₀ (card_ne_zero L)).symm
      · exact absurd h1.2 h2
      · exact absurd ⟨h0, h2⟩ h1
      · rw [mul_zero]
    · rw [datum, if_neg, finsum_eq_zero_of_forall_eq_zero fun f => by rw [dif_neg hy, mul_zero], mul_zero]
      rintro ⟨-, h2⟩
      apply hy
      have h3 := sub_mem (L.smul_mem q.1 h2) (h0 _ (Pair.smul_mem_ker q.mem_max P.hasVal_vec.mem))
      rwa [smul_add, q.smul_inv_smul, ← mulVec_smul, add_sub_cancel_right] at h3
  · rw [datum, if_neg fun h => h0 h.1, finsum_eq_zero_of_forall_eq_zero fun f => by rw [term_neg q χ P h0, zero_mul],
      mul_zero]

end GlobalTheory.GluedExp

namespace GlobalTheory.GluedExp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type}
  [Fintype n] [Fintype n']

open Classical in

theorem glued_col (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (hχ : χ ≠ 1) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]
    (P : Pair k n') :
    latInd (gluedS q 1 P.ker P.vec) L = ((resCard k : ℂ) ^ Fintype.card n)⁻¹ •
      (tensCol (latInd P.ker L) (vecInd L) +
        ∑ Q ∈ withLat L, tensCol (latInd P.ker Q.ker + mainDatum q χ 1 P Q) (charInd χ Q)) := by
  funext x
  conv_lhs => rw [← withCol_split x]
  rw [← datum_eq, datum_expand q χ hχ, Pi.smul_apply, smul_eq_mul, Pi.add_apply, Finset.sum_apply, finsum_split]
  congr 2
  · rw [term_zero, tensCol, vecInd]
    by_cases hy : (fun i => x i (Sum.inr 0)) ∈ L
    · rw [dif_pos hy, if_pos hy, LinearMap.zero_apply, neg_zero, AddChar.map_zero_eq_one]
    · rw [dif_neg hy, if_neg hy]
  · rw [← finsum_ofDual L (fun Q => tensCol (latInd P.ker Q.ker + mainDatum q χ 1 P Q) (charInd χ Q) x)]
    refine finsum_congr fun f => ?_
    rw [term_ne_zero, tensCol, charInd, vecInd, ofDual_lat]
    by_cases hy : (fun i => x i (Sum.inr 0)) ∈ L
    · rw [dif_pos hy, if_pos hy, mul_one, (ofDual_hasVal L f ⟨_, hy⟩).ev_eq]
    · simp only [dif_neg hy, if_neg hy, mul_zero]

theorem glued_sum (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (hχ : χ ≠ 1) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]
    (P : Pair k n') :
    latInd P.ker L + ∑ Q ∈ withLat L, (latInd P.ker Q.ker + mainDatum q χ 1 P Q) =
      ((resCard k : ℂ) ^ Fintype.card n) • latInd P.lat L := by
  classical
  funext x₀
  have hL : latInd P.ker L x₀ + ∑ Q ∈ withLat L, (latInd P.ker Q.ker + mainDatum q χ 1 P Q) x₀ =
      ∑ᶠ f : Module.Dual 𝓀[k] (Red L), term q χ 1 P L f x₀ := by
    rw [finsum_split, term_zero, ← finsum_ofDual L (fun Q => (latInd P.ker Q.ker + mainDatum q χ 1 P Q) x₀)]
    congr 1
    refine finsum_congr fun f => ?_
    rw [term_ne_zero]
  rw [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hL]
  by_cases h0 : ∀ z ∈ P.ker, x₀ *ᵥ z ∈ L
  · rw [finsum_congr (term_pos q χ P h0), finsum_char χ hχ, Red.mk_eq_zero q, latInd]
    have he : q.inv • (imgE q P h0 : n → k) = x₀ *ᵥ P.vec := by
      simp only [imgE, mulVec_smul, q.inv_smul_smul]
    rw [he]
    split_ifs with h1 h2 h2
    · rw [mul_one]
    · refine absurd (fun z hz => ?_) h2
      obtain ⟨s, -, hs⟩ := (Pair.hasVal_iff P.hasVal_vec).1 (P.hasVal_fn ⟨z, hz⟩)
      have := add_mem (h0 _ hs) (L.smul_mem s h1)
      rwa [mulVec_sub, mulVec_smul, sub_add_cancel] at this
    · exact absurd (h2 _ P.hasVal_vec.mem) h1
    · rw [mul_zero]
  · rw [finsum_eq_zero_of_forall_eq_zero (term_neg q χ P h0), latInd,
      if_neg (fun h => h0 fun z hz => h z (P.ker_le hz)), mul_zero]

omit [Fintype n'] in
open Classical in

theorem dualInd_eq (q : Unif k) (L : Submodule 𝒪[k] (n → k)) (η : n → k) :
    dualInd L η = if Lifts L (q.1 • η) 0 then 1 else 0 := by
  refine if_congr ⟨fun h y => ⟨q.1 * ⟨_, h y y.2⟩, ?_, ?_⟩, fun h y hy => ?_⟩ rfl rfl
  · rw [smul_dotProduct]
    rfl
  · rw [map_mul, (residue_eq_zero_iff _).2 q.mem_max, zero_mul, LinearMap.zero_apply]
  · obtain ⟨s, hs, hr⟩ := h ⟨y, hy⟩
    rw [LinearMap.zero_apply] at hr
    obtain ⟨t, rfl⟩ := q.mem_max_iff.1 ((residue_eq_zero_iff s).1 hr)
    rw [smul_dotProduct] at hs
    have : ((t : 𝒪[k]) : k) = η ⬝ᵥ y := mul_left_cancel₀ q.ne_zero hs
    exact this ▸ t.2

omit [Fintype n'] in
open Classical in

theorem cosetInd_pair (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]
    (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}) (η : n → k) :
    cosetInd q (ofDual L f).lat (ofDual L f).red η = if Lifts L (q.1 • η) f.1 then 1 else 0 := by
  have h : (ofDual L f).red = f.1 := dual_ext fun z => rfl
  show cosetInd q L (ofDual L f).red η = _
  rw [h, cosetInd_eq]

omit [Fintype n'] in
open Classical in

theorem finsum_lifts (q : Unif k) (L : Submodule 𝒪[k] (n → k)) (η : n → k) (A : Module.Dual 𝓀[k] (Red L) → ℂ) :
    ∑ᶠ f : Module.Dual 𝓀[k] (Red L), A f * (if Lifts L (q.1 • η) f then 1 else 0) =
      if h : InDual L (q.1 • η) then A (exists_lifts h).choose else 0 := by
  split_ifs with h
  · rw [finsum_eq_single _ (exists_lifts h).choose fun f hf => by
      rw [if_neg fun h' => hf (lifts_unique h' (exists_lifts h).choose_spec), mul_zero],
      if_pos (exists_lifts h).choose_spec, mul_one]
  · exact finsum_eq_zero_of_forall_eq_zero fun f => by
      rw [if_neg fun h' => h (inDual_of_lifts h'), mul_zero]

omit [Fintype n'] in
open Classical in

theorem coset_total (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] (η : n → k) :
    (dualInd L + ∑ Q ∈ withLat L, cosetInd q Q.lat Q.red) η = if InDual L (q.1 • η) then 1 else 0 := by
  have hs := finsum_lifts q L η (fun _ => 1)
  rw [finsum_split] at hs
  simp only [one_mul, dite_eq_ite] at hs
  rw [Pi.add_apply, Finset.sum_apply, dualInd_eq q, ← finsum_ofDual L (fun Q => cosetInd q Q.lat Q.red η)]
  simp only [cosetInd_pair]
  exact hs

end GlobalTheory.GluedExp

namespace GlobalTheory.GluedExp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type}
  [Fintype n] [Fintype n']

theorem glued_row (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] (R : Pair k n') :
    latInd L (gluedS q 1 R.ker R.vec) = tensRow (latInd L R.ker) (dualInd L) +
      ∑ Q ∈ withLat L, tensRow (phiOne Q R) (cosetInd q Q.lat Q.red) := by
  classical
  funext x
  set x' : Matrix n' n k := x.submatrix Sum.inl id
  set η : n → k := x (Sum.inr 0)
  let A : Module.Dual 𝓀[k] (Red L) → ℂ := fun f =>
    if ∀ y : L, R.HasVal (x' *ᵥ (y : n → k)) (f (Red.mk L y)) then 1 else 0
  have hR : (tensRow (latInd L R.ker) (dualInd L) + ∑ Q ∈ withLat L, tensRow (phiOne Q R) (cosetInd q Q.lat Q.red)) x =
      ∑ᶠ f, A f * (if Lifts L (q.1 • η) f then 1 else 0) := by
    rw [Pi.add_apply, Finset.sum_apply, finsum_split,
      ← finsum_ofDual L (fun Q => tensRow (phiOne Q R) (cosetInd q Q.lat Q.red) x)]
    congr 1
    · rw [tensRow, dualInd_eq q]
      congr 1
      exact if_congr ⟨fun h y => Pair.mem_ker.1 (h y y.2), fun h y hy => Pair.mem_ker.2 (h ⟨y, hy⟩)⟩ rfl rfl
    · refine finsum_congr fun f => ?_
      rw [tensRow, cosetInd_pair]
      congr 1
      exact if_congr (maps_iff_hasVal.trans ⟨fun h y => h y _ (ofDual_hasVal L f y),
        fun h y a ⟨hy, ha⟩ => ha ▸ h ⟨y, hy⟩⟩) rfl rfl
  have hm : ∀ y : n → k, x *ᵥ y ∈ gluedS q 1 R.ker R.vec ↔
      ∃ s : 𝒪[k], x' *ᵥ y - s • R.vec ∈ R.ker ∧ η ⬝ᵥ y = q.inv * (s : k) := by
    intro y
    rw [← gluedLat_one, mem_gluedLat]
    refine exists_congr fun s => and_congr Iff.rfl ?_
    simp [Fin.forall_fin_one]
    rfl
  have hq : ∀ a : k, (q.1 : k) * (q.inv * a) = a := fun a => by
    rw [Unif.inv, ← mul_assoc, mul_inv_cancel₀ q.ne_zero, one_mul]
  rw [hR, finsum_lifts, latInd]
  by_cases hD : InDual L (q.1 • η)
  · rw [dif_pos hD]
    have hf₀ := (exists_lifts hD).choose_spec
    set f₀ := (exists_lifts hD).choose
    refine if_congr ⟨fun h y => ?_, fun h y hy => ?_⟩ rfl rfl
    · obtain ⟨s, hs, hr⟩ := hf₀ y
      obtain ⟨s', h1, h2⟩ := (hm y).1 (h y y.2)
      have hss : s' = s := Subtype.ext (by
        rw [hs, smul_dotProduct, h2]
        exact (hq _).symm)
      rw [← hr, ← hss]
      exact (Pair.hasVal_iff R.hasVal_vec).2 ⟨s', rfl, h1⟩
    · obtain ⟨s, hs, hr⟩ := hf₀ ⟨y, hy⟩
      refine (hm y).2 ⟨s, ?_, ?_⟩
      · have h3 := h ⟨y, hy⟩
        rw [← hr] at h3
        obtain ⟨t, ht, hker⟩ := (Pair.hasVal_iff R.hasVal_vec).1 h3
        have hts : t - s ∈ maximalIdeal 𝒪[k] := (residue_eq_zero_iff _).1 (by rw [map_sub, ht, sub_self])
        have h4 := add_mem hker (Pair.smul_mem_ker hts R.hasVal_vec.mem)
        convert h4 using 1
        rw [sub_smul]
        abel
      · rw [smul_dotProduct] at hs
        change (s : k) = (q.1 : k) * (η ⬝ᵥ y) at hs
        rw [hs, Unif.inv, ← mul_assoc, inv_mul_cancel₀ q.ne_zero, one_mul]
  · rw [dif_neg hD, if_neg]
    intro h
    apply hD
    intro y hy
    obtain ⟨s, -, h2⟩ := (hm y).1 (h y hy)
    rw [smul_dotProduct, h2]
    change (q.1 : k) * (q.inv * s) ∈ 𝒪[k]
    rw [hq]
    exact s.2

theorem last_ker (L : Submodule 𝒪[k] (n → k)) (L' : Submodule 𝒪[k] (n' → k)) :
    latInd L (lastKer L') = tensRow (latInd L L') (dualInd L) := by
  classical
  funext x
  rw [tensRow, latInd, latInd, dualInd, ite_zero_mul_ite_zero, mul_one]
  exact if_congr ⟨fun h => ⟨fun y hy => (mem_lastKer.1 (h y hy)).1, fun y hy => (mem_lastKer.1 (h y hy)).2⟩,
    fun h y hy => mem_lastKer.2 ⟨h.1 y hy, h.2 y hy⟩⟩ rfl rfl

theorem last_lat (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] (L' : Submodule 𝒪[k] (n' → k))
    [L'.IsLattice k] :
    latInd L (lastPair q L').lat = tensRow (latInd L L') (dualInd L + ∑ Q ∈ withLat L, cosetInd q Q.lat Q.red) := by
  classical
  funext x
  rw [tensRow, coset_total, latInd, latInd, ite_zero_mul_ite_zero, mul_one]
  have hm : ∀ v : n' ⊕ Fin 1 → k, v ∈ (lastPair q L').lat ↔ v ∘ Sum.inl ∈ L' ∧ q.1 • v (Sum.inr 0) ∈ 𝒪[k] :=
    fun v => by
      rw [Pair.mem_lat_iff]
      simp only [lastPair_hasVal]
      constructor
      · rintro ⟨a, h, s, hs, -⟩
        exact ⟨h, hs ▸ s.2⟩
      · rintro ⟨h, hs⟩
        exact ⟨_, h, ⟨_, hs⟩, rfl, rfl⟩
  refine if_congr ⟨fun h => ⟨fun y hy => ((hm _).1 (h y hy)).1, fun y hy => ?_⟩,
    fun h y hy => (hm _).2 ⟨h.1 y hy, ?_⟩⟩ rfl rfl
  · have h1 := ((hm _).1 (h y hy)).2
    rw [smul_dotProduct]
    exact h1
  · have h1 := h.2 y hy
    rw [smul_dotProduct] at h1
    exact h1

end GlobalTheory.GluedExp

namespace GlobalTheory.GluedExp

theorem finite_expansions : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (χ : AddChar 𝓀[k] ℂ), χ ≠ 1 → ∀ (Λ : Submodule 𝒪[k] (n → k)) [Λ.IsLattice k], (∀ P : Pair k n', latInd (gluedS q 1 P.ker P.vec) Λ = ((resCard k : ℂ) ^ Fintype.card n)⁻¹ • (tensCol (latInd P.ker Λ) (vecInd Λ) + ∑ Q ∈ withLat Λ, tensCol (latInd P.ker Q.ker + mainDatum q χ 1 P Q) (charInd χ Q)) ∧ latInd P.ker Λ + ∑ Q ∈ withLat Λ, (latInd P.ker Q.ker + mainDatum q χ 1 P Q) = ((resCard k : ℂ) ^ Fintype.card n) • latInd P.lat Λ) ∧ (∀ R : Pair k n', latInd Λ (gluedS q 1 R.ker R.vec) = tensRow (latInd Λ R.ker) (dualInd Λ) + ∑ Q ∈ withLat Λ, tensRow (phiOne Q R) (cosetInd q Q.lat Q.red)) ∧ ∀ (L : Submodule 𝒪[k] (n' → k)) [L.IsLattice k], latInd Λ (lastKer L) = tensRow (latInd Λ L) (dualInd Λ) ∧ latInd Λ (lastPair q L).lat = tensRow (latInd Λ L) (dualInd Λ + ∑ Q ∈ withLat Λ, cosetInd q Q.lat Q.red) := by
  intro k _ _ _ _ n n' _ _ _ _ q χ hχ Λ _
  exact ⟨fun P => ⟨glued_col q χ hχ Λ P, glued_sum q χ hχ Λ P⟩, fun R => glued_row q Λ R,
    fun L _ => ⟨last_ker Λ L, last_lat q Λ L⟩⟩

end GlobalTheory.GluedExp
end
end

open GlobalTheory.FinPl GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData ValuativeRel IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedLattice_finite_expansions_localField : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (χ : AddChar 𝓀[k] ℂ), χ ≠ 1 → ∀ (Λ : Submodule 𝒪[k] (n → k)) [Λ.IsLattice k], (∀ P : Pair k n', latInd (gluedS q 1 P.ker P.vec) Λ = ((resCard k : ℂ) ^ Fintype.card n)⁻¹ • (tensCol (latInd P.ker Λ) (vecInd Λ) + ∑ Q ∈ withLat Λ, tensCol (latInd P.ker Q.ker + mainDatum q χ 1 P Q) (charInd χ Q)) ∧ latInd P.ker Λ + ∑ Q ∈ withLat Λ, (latInd P.ker Q.ker + mainDatum q χ 1 P Q) = ((resCard k : ℂ) ^ Fintype.card n) • latInd P.lat Λ) ∧ (∀ R : Pair k n', latInd Λ (gluedS q 1 R.ker R.vec) = tensRow (latInd Λ R.ker) (dualInd Λ) + ∑ Q ∈ withLat Λ, tensRow (phiOne Q R) (cosetInd q Q.lat Q.red)) ∧ ∀ (L : Submodule 𝒪[k] (n' → k)) [L.IsLattice k], latInd Λ (lastKer L) = tensRow (latInd Λ L) (dualInd Λ) ∧ latInd Λ (lastPair q L).lat = tensRow (latInd Λ L) (dualInd Λ + ∑ Q ∈ withLat Λ, cosetInd q Q.lat Q.red) := by
  atlas_forward_decl GlobalTheory.GluedExp.finite_expansions
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SrcGl

variable {D : D7}

def CA (A : HSp D) : Submodule ℂ (GA D A → ℂ) where
  carrier := {φ | GlobalTheory.Unf.IsContAut A φ}
  add_mem' {φ ψ} hφ hψ := ⟨fun γ hγ g => by simp [hφ.1 γ hγ g, hψ.1 γ hγ g], hφ.2.add hψ.2⟩
  zero_mem' := ⟨fun _ _ _ => rfl, continuous_const⟩
  smul_mem' c φ hφ := ⟨fun γ hγ g => by simp [hφ.1 γ hγ g], continuous_const.mul hφ.2⟩

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {n : Type} [Fintype n] [DecidableEq n]

theorem rep_mem_CA {A : HSp D} (α : Frame p A n) (g : GL n k) {φ : GA D A → ℂ} (h : φ ∈ CA A) : α.rep g φ ∈ CA A :=
  ⟨fun γ hγ x => by
    change φ (γ * x * α.gl g) = φ (x * α.gl g)
    rw [mul_assoc, h.1 γ hγ], h.2.comp (continuous_mul_right _)⟩

def caRep {A : HSp D} (α : Frame p A n) : Representation ℂ (GL n k) (CA A) where
  toFun g := (α.rep g).restrict fun _ h => rep_mem_CA α g h
  map_one' := by ext φ x; simp
  map_mul' g h := by ext φ x; simp

@[simp] theorem caRep_apply {A : HSp D} (α : Frame p A n) (g : GL n k) (φ : CA A) :
    ((caRep α g φ : CA A) : GA D A → ℂ) = α.rep g φ := rfl

def blkHom : Matrix n n k →* Matrix (n ⊕ Fin 1) (n ⊕ Fin 1) k where
  toFun x := fromBlocks x 0 0 1
  map_one' := by simp
  map_mul' x y := by simp [fromBlocks_multiply]

def blk : GL n k →* GL (n ⊕ Fin 1) k := Units.map blkHom

@[simp] theorem blk_val (g : GL n k) : (blk g).val = fromBlocks g.val (0 : Matrix n (Fin 1) k) 0 1 := rfl

end GlobalTheory.FinPl.SrcGl
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
open GlobalTheory.FinPl GlobalTheory.FinPl.SrcGl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SrcTheta

section Lift

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S A L T : HSp D} (o : OrthDec S A L) {χS χT : (AE D)ˣ →* Circle}
  {om : Om S T}

theorem contAut_ker (hW : IsWeilDatumO ψ S T χS χT om) {φ : GA D A → ℂ} {Ξ : WO S T → ℂ} (hφ : IsContAut A φ)
    (hΞ : IsThetaFunO ψ S T Ξ) (h : GA D T) (u : WO L T) :
    IsContAut A fun a => φ a * om (o.emb (a, 1), h) Ξ ((o.resS T).symm (0, u)) := by
  refine ⟨fun γ hγ a => ?_, hφ.2.mul ((hW.om_cont Ξ hΞ _).comp
    ((o.continuous_emb.comp (continuous_id.prodMk continuous_const)).prodMk continuous_const))⟩
  have e := GlobalTheory.T.weilRepresentation_rational_translate_substitution D ψ _ _ _ _ _ hW Ξ hΞ _ (o.emb_mem_GQ hγ (one_mem _)) 1 (one_mem _) (o.emb (a, 1)) h
    ((o.resS T).symm (0, u))
  rw [← map_mul, Prod.mk_mul_mk, one_mul, one_mul, inv_one, mt_one, Matrix.one_mul] at e
  beta_reduce
  rw [hφ.1 γ hγ, e]
  congr 2
  rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add, Matrix.mul_assoc, OrthDec.pB_emb, mt_one, Matrix.one_mul]

theorem liftA_add_left (hA : CoCpt A) (vA : Vol A) (hW : IsWeilDatumO ψ S T χS χT om) {φ φ' : GA D A → ℂ}
    {Ξ : WO S T → ℂ} (hφ : IsContAut A φ) (hφ' : IsContAut A φ') (hΞ : IsThetaFunO ψ S T Ξ) :
    liftA o om vA (φ + φ') Ξ = liftA o om vA φ Ξ + liftA o om vA φ' Ξ := by
  funext h w
  simp only [liftA, Pi.add_apply, add_mul]
  exact integral_add (Comm.IsContAut.integrableOn hA vA (contAut_ker o hW hφ hΞ h _))
    (Comm.IsContAut.integrableOn hA vA (contAut_ker o hW hφ' hΞ h _))

theorem liftA_add_right (hA : CoCpt A) (vA : Vol A) (hW : IsWeilDatumO ψ S T χS χT om) {φ : GA D A → ℂ}
    {Ξ Ξ' : WO S T → ℂ} (hφ : IsContAut A φ) (hΞ : IsThetaFunO ψ S T Ξ) (hΞ' : IsThetaFunO ψ S T Ξ') :
    liftA o om vA φ (Ξ + Ξ') = liftA o om vA φ Ξ + liftA o om vA φ Ξ' := by
  funext h w
  simp only [liftA, map_add, Pi.add_apply, mul_add]
  exact integral_add (Comm.IsContAut.integrableOn hA vA (contAut_ker o hW hφ hΞ h _))
    (Comm.IsContAut.integrableOn hA vA (contAut_ker o hW hφ hΞ' h _))

theorem liftA_smul_left (vA : Vol A) (c : ℂ) (φ : GA D A → ℂ) (Ξ : WO S T → ℂ) :
    liftA o om vA (c • φ) Ξ = c • liftA o om vA φ Ξ := by
  funext h w
  simp only [liftA, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _

theorem liftA_smul_right (vA : Vol A) (c : ℂ) (φ : GA D A → ℂ) (Ξ : WO S T → ℂ) :
    liftA o om vA φ (c • Ξ) = c • liftA o om vA φ Ξ := by
  funext h w
  simp only [liftA, map_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
  exact integral_const_mul _ _

theorem liftA_equiv (vA : Vol A) (hW : IsWeilDatumO ψ S T χS χT om) {φ : GA D A → ℂ} {Ξ : WO S T → ℂ}
    (hφ : IsContAut A φ) (hΞ : IsThetaFunO ψ S T Ξ) (a : GA D A) :
    liftA o om vA (fun x => φ (x * a)) (om (o.emb (a, 1), 1) Ξ) = liftA o om vA φ Ξ := by
  funext h w
  simp only [liftA]
  refine Eq.trans ?_ (Comm.integral_right vA (contAut_ker o hW hφ hΞ h w).1 a)
  congr 1
  funext x
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]

end Lift

theorem exists_linear_of_rel {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (P : Submodule ℂ M) (R : M → N → Prop) (hex : ∀ x ∈ P, ∃! y, R x y)
    (hlin : ∀ (c : ℂ) x y x' y', R x y → R x' y' → R (c • x + x') (c • y + y')) :
    ∃ G : M →ₗ[ℂ] N, (∀ x, ∃ x', R x' (G x)) ∧ ∀ x ∈ P, R x (G x) := by
  choose F hF hFu using fun x : P => hex x.1 x.2
  have hc : ∀ (c : ℂ) (x x' : P), F (c • x + x') = c • F x + F x' := fun c x x' =>
    (hFu (c • x + x') _ (hlin c _ _ _ _ (hF x) (hF x'))).symm
  have h0 : F 0 = 0 := by
    have := hc 1 0 0
    simp only [one_smul, add_zero] at this
    exact left_eq_add.1 this
  let F' : P →ₗ[ℂ] N :=
    { toFun := F
      map_add' := fun x y => by simpa using hc 1 x y
      map_smul' := fun c x => by simpa [h0] using hc c x 0 }
  obtain ⟨Q, hQ⟩ := P.exists_isCompl
  refine ⟨F' ∘ₗ P.linearProjOfIsCompl Q hQ, fun x => ⟨_, hF _⟩, fun x hx => ?_⟩
  have e : P.linearProjOfIsCompl Q hQ x = ⟨x, hx⟩ := Submodule.linearProjOfIsCompl_apply_left hQ ⟨x, hx⟩
  rw [LinearMap.comp_apply, e]
  exact hF ⟨x, hx⟩

theorem exists_theta : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → CoCpt A → ∀ (vA : Vol A) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n), IsSumFrame o ζ α α₀ → ∃ lS : kˣ →* ℂˣ, (CharUnramAt D χT p.v → IsUnram lS) ∧ ∀ (LS : Lat S) (LT : Lat T) (f₀ : WO S T → ℂ), IsSelfDualC S LS → IsSelfDualC T LT → Vac ψ S T LS LT (· = p.v) f₀ → ∃ θ : GlobalTheory.FinPl.SrcGl.CA A →ₗ[ℂ] (Matrix n (n' ⊕ Fin 1) k → ℂ) →ₗ[ℂ] (GA D T → WO L T → ℂ), (∀ (v : GlobalTheory.FinPl.SrcGl.CA A) (Φ : Matrix n (n' ⊕ Fin 1) k → ℂ) (f : WO S T → ℂ), Over ψ α₀ β LS LT f₀ Φ f → θ v Φ = liftA o om vA v f) ∧ ∀ (g : GL n' k) (v : GlobalTheory.FinPl.SrcGl.CA A) (Φ : Matrix n (n' ⊕ Fin 1) k → ℂ), Φ ∈ SB (Matrix n (n' ⊕ Fin 1) k) → θ (GlobalTheory.FinPl.SrcGl.caRep α g v) (fun x => Φ (x * (GlobalTheory.FinPl.SrcGl.blk g).val)) = ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ • θ v Φ := by
  intro D k _ _ _ _ p n n' _ _ _ _ ψ S A L T o ζ _ hA vA χS χT om hW α α₀ β hsum
  obtain ⟨lS, lT, hlS, -, hlin⟩ := GlobalTheory.T.splitPlace_linearModel_latticeVacuum_base D k p ψ S T χS χT om hW
  refine ⟨lS, hlS, fun LS LT f₀ hLS hLT hvac => ?_⟩
  obtain ⟨hex, hth, -⟩ := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n (n' ⊕ Fin 1) ψ hW.std S T α₀ β LS LT hLS hLT f₀ hvac
  obtain ⟨G, hG, hGP⟩ := exists_linear_of_rel (SB (Matrix n (n' ⊕ Fin 1) k)) (Over ψ α₀ β LS LT f₀) hex
    (fun c x y x' y' h h' => (hlin n _ α₀ β LS LT f₀ x y h).2.2 c x' y' h')
  have hGt : ∀ Φ, IsThetaFunO ψ S T (G Φ) := fun Φ => (hG Φ).elim fun x hx => (hth _ _ hx).1
  have hGf : ∀ Φ f, Over ψ α₀ β LS LT f₀ Φ f → G Φ = f := fun Φ f h =>
    (hex Φ h.2.2.2.1).unique (hGP Φ h.2.2.2.1) h
  let θ : CA A →ₗ[ℂ] (Matrix n (n' ⊕ Fin 1) k → ℂ) →ₗ[ℂ] (GA D T → WO L T → ℂ) :=
    LinearMap.mk₂ ℂ (fun v Φ => liftA o om vA v (G Φ))
      (fun v v' Φ => liftA_add_left o hA vA hW v.2 v'.2 (hGt Φ))
      (fun c v Φ => liftA_smul_left o vA c v (G Φ))
      (fun v Φ Φ' => by rw [map_add]; exact liftA_add_right o hA vA hW v.2 (hGt Φ) (hGt Φ'))
      (fun c v Φ => by rw [map_smul]; exact liftA_smul_right o vA c v (G Φ))
  have hθ : ∀ (v : CA A) Φ, θ v Φ = liftA o om vA v (G Φ) := fun _ _ => rfl
  refine ⟨θ, fun v Φ f h => by rw [hθ, hGf Φ f h], fun g v Φ hΦ => ?_⟩
  have h1 := (hlin n _ α₀ β LS LT f₀ Φ _ (hGP Φ hΦ)).1 (blk g) 1
  have hdet : Matrix.GeneralLinearGroup.det (blk g) = Matrix.GeneralLinearGroup.det g := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply]
  have hemb : α₀.gl (blk g) = o.emb (α.gl g, 1) := by
    rw [Comm.emb_gl hsum]
    congr 1
  have hfun : (fun x : Matrix n (n' ⊕ Fin 1) k => (lS (Matrix.GeneralLinearGroup.det (blk g)) : ℂ) *
      (lT (Matrix.GeneralLinearGroup.det (1 : GL n k)) : ℂ) * Φ (((1 : GL n k)⁻¹ : GL n k).val * x * (blk g).val)) =
      (lS (Matrix.GeneralLinearGroup.det g) : ℂ) • fun x => Φ (x * (blk g).val) := by
    funext x
    simp only [hdet, map_one, Units.val_one, mul_one, inv_one, Matrix.one_mul, Pi.smul_apply, smul_eq_mul]
  rw [hfun, hemb, map_one] at h1
  have h2 : θ (caRep α g v) ((lS (Matrix.GeneralLinearGroup.det g) : ℂ) • fun x => Φ (x * (blk g).val)) = θ v Φ := by
    rw [hθ, hθ, hGf _ _ h1]
    exact liftA_equiv o vA hW v.2 (hGt Φ) (α.gl g)
  rw [← h2, map_smul, inv_smul_smul₀ (Units.ne_zero _)]

end GlobalTheory.FinPl.SrcTheta

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
open GlobalTheory.FinPl GlobalTheory.FinPl.SrcGl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bilinear_equivariant_orthogonalSummandLift : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → CoCpt A → ∀ (vA : Vol A) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n), IsSumFrame o ζ α α₀ → ∃ lS : kˣ →* ℂˣ, (CharUnramAt D χT p.v → IsUnram lS) ∧ ∀ (LS : Lat S) (LT : Lat T) (f₀ : WO S T → ℂ), IsSelfDualC S LS → IsSelfDualC T LT → Vac ψ S T LS LT (· = p.v) f₀ → ∃ θ : GlobalTheory.FinPl.SrcGl.CA A →ₗ[ℂ] (Matrix n (n' ⊕ Fin 1) k → ℂ) →ₗ[ℂ] (GA D T → WO L T → ℂ), (∀ (v : GlobalTheory.FinPl.SrcGl.CA A) (Φ : Matrix n (n' ⊕ Fin 1) k → ℂ) (f : WO S T → ℂ), Over ψ α₀ β LS LT f₀ Φ f → θ v Φ = liftA o om vA v f) ∧ ∀ (g : GL n' k) (v : GlobalTheory.FinPl.SrcGl.CA A) (Φ : Matrix n (n' ⊕ Fin 1) k → ℂ), Φ ∈ SB (Matrix n (n' ⊕ Fin 1) k) → θ (GlobalTheory.FinPl.SrcGl.caRep α g v) (fun x => Φ (x * (GlobalTheory.FinPl.SrcGl.blk g).val)) = ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ • θ v Φ := by
  first | exact @GlobalTheory.FinPl.SrcTheta.exists_theta | exact GlobalTheory.FinPl.SrcTheta.exists_theta | (intros; apply GlobalTheory.FinPl.SrcTheta.exists_theta <;> assumption)
end

section
open GlobalTheory.FinPl GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_tensor_indicator_character_facts : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'], (∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), Ψ ∈ SB (Matrix n n' k) → a ∈ SB (n → k) → GlobalTheory.FinPl.tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) ∧ (∀ (Λ : Submodule 𝒪[k] (n → k)), Λ.IsLattice k → GlobalTheory.FinPl.vecInd Λ ∈ SB (n → k)) ∧ ∀ (χ : AddChar 𝓀[k] ℂ) (Q : Pair k n), GlobalTheory.FinPl.charInd χ Q ∈ SB (n → k) := by
  first | exact @GlobalTheory.FinPl.sb_facts | exact GlobalTheory.FinPl.sb_facts | (intros; apply GlobalTheory.FinPl.sb_facts <;> assumption)
end

section
open GlobalTheory.FinPl GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedCharacter_det_latticeStabilizer_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (L : Submodule 𝒪[k] (n → k)), L.IsLattice k → ∀ g ∈ latStab L, ∀ μ : kˣ →* ℂˣ, IsUnram μ → μ (Matrix.GeneralLinearGroup.det g) = 1 := by
  first | exact @GlobalTheory.LatPair.Det.isUnram_det_latStab | exact GlobalTheory.LatPair.Det.isUnram_det_latStab | (intros; apply GlobalTheory.LatPair.Det.isUnram_det_latStab <;> assumption)
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SrcGl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem tensCol_mul_blk (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ) (g : GL n' k) (x : Matrix n (n' ⊕ Fin 1) k) :
    tensCol Ψ a (x * (blk g).val) = tensCol (fun x₀ => Ψ (x₀ * g.val)) a x := by
  simp only [tensCol, blk_val]
  congr 2
  · ext i j
    simp [Matrix.mul_apply, fromBlocks, Fintype.sum_sum_type]
  · ext i
    simp [Matrix.mul_apply, fromBlocks, Fintype.sum_sum_type]

theorem phiOne_smul_left (g : GL n' k) (P : Pair k n') (Q : Pair k n) (x : Matrix n n' k) :
    phiOne (g • P) Q x = phiOne P Q (x * g.val) := by
  classical
  have hs : ∀ (h : GL n' k) (y : n' → k), h • y = h.val *ᵥ y := fun _ _ => rfl
  unfold phiOne
  congr 1
  apply propext
  rw [maps_iff_hasVal, maps_iff_hasVal]
  constructor
  · intro h y a hy
    have := h (g • y) a (hy.gl_smul g)
    simpa [hs, Matrix.mulVec_mulVec] using this
  · intro h y a hy
    have := h (g⁻¹ • y) a (Pair.smul_hasVal.1 hy)
    simpa [hs, Matrix.mulVec_mulVec] using this

end GlobalTheory.FinPl.SrcGl

namespace GlobalTheory.FinPl.SrcGl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {n' : Type} [Fintype n'] [DecidableEq n']

theorem coe_FFStar {A : HSp D} (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (φ : Form k n' (CA A)) (P : Pair k n') :
    ((FFStar q χ φ P : CA A) : GA D A → ℂ) = FFStar q χ (fun P => (φ P : GA D A → ℂ)) P := by
  simp [FFStar_apply]

def toCA {A : HSp D} (φ : Form k n' (GA D A → ℂ)) (h : ∀ P, IsContAut A (φ P)) : Form k n' (CA A) :=
  fun P => ⟨φ P, h P⟩

theorem toCA_ram {A : HSp D} {α : Frame p A n'} {φ : Form k n' (GA D A → ℂ)} (hφ : IsRam α φ) :
    toCA φ hφ.2.2 ∈ Mram k n' (CA A) ∧ toCA φ hφ.2.2 ∈ EqForm (caRep α) := by
  letI := Fintype.ofFinite 𝓀[k]ˣ
  refine ⟨(mem_Mram _).2 fun P => Subtype.ext ?_, fun g P => Subtype.ext (hφ.1 g P)⟩
  simpa [toCA] using (mem_Mram φ).1 hφ.2.1 P

theorem exists_lat_eq (P : Pair k n') : ∃ P' : Pair k n', P'.lat = P.ker := by
  have h1 : Module.finrank 𝓀[k] (Red P.ker) = Module.finrank 𝓀[k] (Red P.lat) := by
    rw [Red.finrank_eq, Red.finrank_eq]
  have h2 : Nontrivial (Red P.lat) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact P.red_ne (LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero])
  have h3 : 0 < Module.finrank 𝓀[k] (Red P.ker) := h1 ▸ Module.finrank_pos
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.1 h3
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual 𝓀[k] (Red P.ker), f x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx ((Module.forall_dual_apply_eq_zero_iff 𝓀[k] x).1 h)
  exact ⟨ofDual P.ker ⟨f, fun h0 => hf (by rw [h0]; rfl)⟩, ofDual_lat _ _⟩

variable {n : Type} [Fintype n] [DecidableEq n]

def tensL (a : (n → k) → ℂ) : (Matrix n n' k → ℂ) →ₗ[ℂ] (Matrix n (n' ⊕ Fin 1) k → ℂ) where
  toFun Ψ := tensCol Ψ a
  map_add' Ψ Ψ' := by ext x; simp [tensCol, add_mul]
  map_smul' c Ψ := by ext x; simp [tensCol, mul_assoc]

@[simp] theorem tensL_apply (a : (n → k) → ℂ) (Ψ : Matrix n n' k → ℂ) : tensL a Ψ = tensCol Ψ a := rfl

theorem tensCol_add (Ψ Ψ' : Matrix n n' k → ℂ) (a : (n → k) → ℂ) : tensCol (Ψ + Ψ') a = tensCol Ψ a + tensCol Ψ' a :=
  (tensL a).map_add Ψ Ψ'

end GlobalTheory.FinPl.SrcGl

open GlobalTheory.FinPl GlobalTheory.FinPl.SrcGl in
theorem GlobalTheory.FinPl.sourceGlued : ∀ D : D7, GlobalTheory.FinPl.SourceGlued D := by
  intro D k _ _ _ _ p n n' _ _ _ _ q χ₀ hχ χ hχχ ψ S A L T o ζ hL hA vA χS χT om hW _ hT α α₀ β hsum P P₁ Λ _
  obtain ⟨lS, hlS, hθ⟩ := GlobalTheory.T.exists_bilinear_equivariant_orthogonalSummandLift D k p n n' ψ S A L T o ζ hL hA vA χS χT om hW α α₀ β hsum
  have hdet : ∀ L' : Submodule 𝒪[k] (n' → k), L'.IsLattice k → ∀ g ∈ latStab L',
      ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) = 1 := fun L' hL' g hg => by
    rw [GlobalTheory.T.unramifiedCharacter_det_latticeStabilizer_eq_one k n' L' hL' g hg lS (hlS hT), Units.val_one]
  have hsb := GlobalTheory.T.schwartzBruhat_tensor_indicator_character_facts k n n'

  have hinv : ∀ (θ : CA A →ₗ[ℂ] (Matrix n (n' ⊕ Fin 1) k → ℂ) →ₗ[ℂ] (GA D T → WO L T → ℂ)),
      (∀ (g : GL n' k) (v : CA A) (Φ : Matrix n (n' ⊕ Fin 1) k → ℂ), Φ ∈ SB (Matrix n (n' ⊕ Fin 1) k) →
        θ (caRep α g v) (fun x => Φ (x * (blk g).val)) = ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ • θ v Φ) →
      ∀ a ∈ SB (n → k), ∀ L' : Submodule 𝒪[k] (n' → k), L'.IsLattice k →
        GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.IsLiftInv (caRep α) (θ.compl₂ (tensL a)) L' := by
    intro θ hθe a ha L' hL' g hg v Ψ hΨ
    simp only [LinearMap.compl₂_apply, tensL_apply]
    have := hθe g v _ (hsb.1 Ψ a hΨ ha)
    rw [hdet L' hL' g hg, inv_one, one_smul] at this
    refine Eq.trans (congrArg _ ?_) this
    funext x
    exact (tensCol_mul_blk Ψ a g x).symm
  obtain ⟨P', hP'⟩ := exists_lat_eq P
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL n' k) P' P₁
  refine ⟨⟨((resCard k : ℂ) ^ Fintype.card n)⁻¹ * ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ), ?_⟩, ?_⟩
  · intro LS LT f₀ Ξ Ξ' hΞ hΞ' φ hφ
    obtain ⟨θ, hθv, hθe⟩ := hθ LS LT f₀ hΞ.1 hΞ.2.1 hΞ.2.2.1
    obtain ⟨hram, heq⟩ := toCA_ram hφ
    set φc := toCA φ hφ.2.2 with hφc
    have hχ1 : χ ≠ 1 := hχχ ▸ resChar_ne_one hχ q
    rw [show liftA o om vA (φ P) Ξ = θ (φc P) _ from (hθv (φc P) _ _ hΞ).symm,
      ((GlobalTheory.T.gluedLattice_finite_expansions_localField k n n' q χ hχ1 Λ).1 P).1]
    have e0 : θ (φc P) (tensCol (latInd P.ker Λ) (vecInd Λ)) = 0 :=
      GlobalTheory.LastSteps.lift_latInd P hram heq (hinv θ hθe _ (hsb.2.1 Λ inferInstance) P.ker inferInstance) Λ
    have e1 : ∀ Q ∈ withLat Λ, θ (φc P) (tensCol (latInd P.ker Q.ker + GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mainDatum q χ 1 P Q)
        (charInd χ Q)) = ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • liftA o om vA (FFStar q χ φ P₁) (Ξ' Q) := by
      intro Q hQ
      have hI := hinv θ hθe _ (hsb.2.2 χ Q) P.ker inferInstance
      have a0 : θ (φc P) (tensCol (latInd P.ker Q.ker) (charInd χ Q)) = 0 :=
        GlobalTheory.LastSteps.lift_latInd P hram heq hI Q.ker
      have a1 := GlobalTheory.LastSteps.lift_mainDatum q χ 1 heq hI Q rfl hP'
      simp only [LinearMap.compl₂_apply, tensL_apply, map_one, Module.End.one_apply] at a1
      have a2 := hθe g⁻¹ (FFStar q χ φc P₁) _ (hΞ' Q hQ).2.2.2.1
      have b1 : caRep α g⁻¹ (FFStar q χ φc P₁) = FFStar q χ φc P' := by
        rw [← hg, FFStar_mem_EqForm q χ heq g P', ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_apply]
      have b2 : (fun x => tensCol (phiOne P₁ Q) (charInd χ Q) (x * (blk g⁻¹).val)) = tensCol (phiOne P' Q) (charInd χ Q) := by
        funext x
        rw [tensCol_mul_blk]
        congr 1
        funext x₀
        rw [← hg, phiOne_smul_left, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      rw [b1, b2, hθv _ _ _ (hΞ' Q hQ), coe_FFStar] at a2
      rw [tensCol_add, map_add, a0, zero_add, a1, a2, map_inv, map_inv, Units.val_inv_eq_inv_val, inv_inv]
      rfl
    rw [map_smul, map_add, map_sum, e0, zero_add, Finset.sum_congr rfl e1, ← Finset.smul_sum, smul_smul]
  · intro LS LT f₀ Ξ a hor φ hφ
    obtain ⟨L₁, hL₁, hO⟩ : ∃ L₁ : Submodule 𝒪[k] (n' → k), (L₁ = P.lat ∨ L₁ = P.ker) ∧
        Over ψ α₀ β LS LT f₀ (tensCol (latInd L₁ Λ) a) Ξ := by
      rcases hor with h | h
      exacts [⟨_, Or.inl rfl, h⟩, ⟨_, Or.inr rfl, h⟩]
    haveI : L₁.IsLattice k := by rcases hL₁ with rfl | rfl <;> infer_instance
    obtain ⟨θ, hθv, hθe⟩ := hθ LS LT f₀ hO.1 hO.2.1 hO.2.2.1
    obtain ⟨hram, heq⟩ := toCA_ram hφ
    set φc := toCA φ hφ.2.2 with hφc
    rw [show liftA o om vA (φ P) Ξ = θ (φc P) _ from (hθv (φc P) _ _ hO).symm]
    have hinvL : ∀ g ∈ latStab L₁, ∀ w, θ (caRep α g w) (tensCol (latInd L₁ Λ) a) = θ w (tensCol (latInd L₁ Λ) a) := by
      intro g hg w
      have := hθe g w _ hO.2.2.2.1
      rw [hdet L₁ inferInstance g hg, inv_one, one_smul] at this
      refine Eq.trans (congrArg _ ?_) this
      funext x
      rw [tensCol_mul_blk]
      congr 1
      funext x₀
      exact (GlobalTheory.LastSteps.latInd_mul hg Λ x₀).symm
    have hv : formOf (caRep α) P (evalEquiv (caRep α) P ⟨φc, heq⟩) = φc :=
      congrArg Subtype.val ((evalEquiv (caRep α) P).left_inv ⟨φc, heq⟩)
    exact (GlobalTheory.PairOp.vanishing q).invariant_eq_zero (caRep α) P (evalEquiv (caRep α) P ⟨φc, heq⟩) (hv.symm ▸ hram) _
      (θ.flip (tensCol (latInd L₁ Λ) a)) (by
        rcases hL₁ with rfl | rfl
        exacts [Or.inl fun g hg w => hinvL g hg w, Or.inr fun g hg w => hinvL g hg w])
end
end
