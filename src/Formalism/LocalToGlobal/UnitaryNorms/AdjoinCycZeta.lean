import Formalism.LocalToGlobal.UnitaryNorms.RealCyclotomicTwoPower
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.EqZeroOfNegEq

section
noncomputable section

open IntermediateField NumberField

namespace Formalism.L2.Host

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

theorem sqQ_eq {m : ℤ} {w : Qb} (hw : w ^ 2 = (m : Qb)) : sqQ m = ℚ⟮w⟯ := by
  apply le_antisymm
  · show adjoin ℚ (sqrts m) ≤ _
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    have hz' : z ^ 2 = w ^ 2 := by
      rw [hw]
      exact hz
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hz' with rfl | rfl
    · exact IntermediateField.mem_adjoin_simple_self ℚ z
    · exact neg_mem (IntermediateField.mem_adjoin_simple_self ℚ w)
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact IntermediateField.subset_adjoin ℚ (sqrts m) hw

theorem pow_add_inv_pow_mem {w : Qb} (hw : w ≠ 0) (k : ℕ) : w ^ k + w⁻¹ ^ k ∈ ℚ⟮w + w⁻¹⟯ := by
  have key : ∀ n : ℕ, w ^ n + w⁻¹ ^ n ∈ ℚ⟮w + w⁻¹⟯ ∧ w ^ (n + 1) + w⁻¹ ^ (n + 1) ∈ ℚ⟮w + w⁻¹⟯ := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp only [pow_zero]
        exact add_mem (one_mem _) (one_mem _)
      · simp only [zero_add, pow_one]
        exact IntermediateField.mem_adjoin_simple_self ℚ _
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have h1 : w * w⁻¹ = 1 := mul_inv_cancel₀ hw
      have e : w ^ (n + 1 + 1) + w⁻¹ ^ (n + 1 + 1) =
          (w + w⁻¹) * (w ^ (n + 1) + w⁻¹ ^ (n + 1)) - (w ^ n + w⁻¹ ^ n) := by
        linear_combination (-(w ^ n + w⁻¹ ^ n)) * h1
      rw [e]
      exact sub_mem (mul_mem (IntermediateField.mem_adjoin_simple_self ℚ _) ih.2) ih.1
  exact (key k).1

theorem cycQplus_eq {N : ℕ} [NeZero N] {w : Qb} (hw : IsPrimitiveRoot w N) :
    cycQplus N = ℚ⟮w + w⁻¹⟯ := by
  have hw0 : w ≠ 0 := hw.ne_zero (NeZero.ne N)
  apply le_antisymm
  · show adjoin ℚ ((fun z => z + z⁻¹) '' mus N) ≤ _
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨i, -, rfl⟩ := hw.eq_pow_of_pow_eq_one hz
    show w ^ i + (w ^ i)⁻¹ ∈ ℚ⟮w + w⁻¹⟯
    rw [← inv_pow]
    exact pow_add_inv_pow_mem hw0 i
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact IntermediateField.subset_adjoin ℚ ((fun z : Qb => z + z⁻¹) '' mus N) ⟨w, hw.pow_eq_one, rfl⟩

theorem cycQ_eq {N : ℕ} [NeZero N] {w : Qb} (hw : IsPrimitiveRoot w N) : cycQ N = ℚ⟮w⟯ := by
  apply le_antisymm
  · show adjoin ℚ (mus N) ≤ _
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    obtain ⟨i, -, rfl⟩ := hw.eq_pow_of_pow_eq_one hz
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ w) i
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact IntermediateField.subset_adjoin ℚ (mus N) hw.pow_eq_one

theorem adjoin_pair_eq_sup (x y : Qb) : adjoin ℚ {x, y} = ℚ⟮x⟯ ⊔ ℚ⟮y⟯ := by
  rw [Set.insert_eq]
  exact IntermediateField.gc.l_sup

theorem EQ_eq_adjoin (e q d : ℕ) : EQ e q d =
    adjoin ℚ ((sqrts (-(q : ℤ)) ∪ sqrts (-(d : ℤ))) ∪ (fun z => z + z⁻¹) '' mus (2 ^ (e + 2))) := by
  show sqQ (-(q : ℤ)) ⊔ sqQ (-(d : ℤ)) ⊔ cycQplus (2 ^ (e + 2)) = _
  rw [sqQ, sqQ, cycQplus, ← IntermediateField.gc.l_sup, ← IntermediateField.gc.l_sup]
  rfl

theorem pow_neg_val {N : ℕ} [NeZero N] {z : Qb} (hz : z ^ N = 1) (u : ZMod N) :
    z ^ (-u).val = z⁻¹ ^ u.val := by
  have hdvd : N ∣ (-u).val + u.val := by
    rw [← CharP.cast_eq_zero_iff (ZMod N) N]
    simp
  obtain ⟨c, hc⟩ := hdvd
  have h1 : z ^ (-u).val * z ^ u.val = 1 := by rw [← pow_add, hc, pow_mul, hz, one_pow]
  rw [inv_pow]
  exact eq_inv_of_mul_eq_one_left h1

theorem ActsAs.unique {e q d : ℕ} {s s' : EQ e q d →ₐ[ℚ] Qb} {g : GG e}
    (h : ActsAs e q d s g) (h' : ActsAs e q d s' g) : s = s' := by
  obtain ⟨h1, h2, u, hu, hs⟩ := h
  obtain ⟨h1', h2', u', hu', hs'⟩ := h'
  refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (EQ_eq_adjoin e q d) ?_
  intro x hx
  rcases hx with (hx | hx) | ⟨z, hz, hzx⟩
  · exact (h1 _ hx).trans (h1' _ hx).symm
  · exact (h2 _ hx).trans (h2' _ hx).symm
  · have hz1 : z ^ (2 ^ (e + 2)) = 1 := hz
    have hz' : z⁻¹ ^ (2 ^ (e + 2)) = 1 := by rw [inv_pow, hz1, inv_one]
    have hval : z ^ (u : ZMod (2 ^ (e + 2))).val + z⁻¹ ^ (u : ZMod (2 ^ (e + 2))).val =
        z ^ (u' : ZMod (2 ^ (e + 2))).val + z⁻¹ ^ (u' : ZMod (2 ^ (e + 2))).val := by
      have hq : (hcl e u : HGrp e) = hcl e u' := hu.trans hu'.symm
      rw [hcl, hcl, QuotientGroup.eq, Subgroup.mem_zpowers_iff] at hq
      obtain ⟨k, hk⟩ := hq
      rcases Int.even_or_odd k with he | ho
      · rw [he.neg_one_zpow, eq_comm, inv_mul_eq_one] at hk
        rw [hk]
      · rw [ho.neg_one_zpow, eq_comm, inv_mul_eq_iff_eq_mul, mul_neg_one] at hk
        rw [hk, Units.val_neg, pow_neg_val hz1, pow_neg_val hz', inv_inv, add_comm]
    exact ((hs _ z hz hzx.symm).trans hval).trans (hs' _ z hz hzx.symm).symm

theorem ActsAs.snd {e q d : ℕ} {s : EQ e q d →ₐ[ℚ] Qb} {g : GG e} (h : ActsAs e q d s g)
    (u' : (ZMod (2 ^ (e + 2)))ˣ) (hu' : hcl e u' = g.2) (x : EQ e q d) (z : Qb) (hz : z ∈ mus (2 ^ (e + 2)))
    (hx : (x : Qb) = z + z⁻¹) :
    s x = z ^ (u' : ZMod (2 ^ (e + 2))).val + z⁻¹ ^ (u' : ZMod (2 ^ (e + 2))).val := by
  obtain ⟨-, -, u, hu, hs⟩ := h
  rw [hs x z hz hx]
  have hq : (hcl e u : HGrp e) = hcl e u' := hu.trans hu'.symm
  rw [hcl, hcl, QuotientGroup.eq, Subgroup.mem_zpowers_iff] at hq
  obtain ⟨k, hk⟩ := hq
  have hz1 : z ^ (2 ^ (e + 2)) = 1 := hz
  have hz' : z⁻¹ ^ (2 ^ (e + 2)) = 1 := by rw [inv_pow, hz1, inv_one]
  rcases Int.even_or_odd k with he | ho
  · rw [he.neg_one_zpow, eq_comm, inv_mul_eq_one] at hk
    rw [hk]
  · rw [ho.neg_one_zpow, eq_comm, inv_mul_eq_iff_eq_mul, mul_neg_one] at hk
    rw [hk, Units.val_neg, pow_neg_val hz1, pow_neg_val hz', inv_inv, add_comm]

section Layer

variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

theorem map_a_sq (h : IsLayer (e + 2) q d ζ a b) (φ : L →ₐ[ℚ] Qb) :
    φ a ^ 2 = ((-(q : ℤ) : ℤ) : Qb) := by
  rw [← map_pow, h.2.1]
  simp

theorem map_b_sq (h : IsLayer (e + 2) q d ζ a b) (φ : L →ₐ[ℚ] Qb) :
    φ b ^ 2 = ((-(d : ℤ) : ℤ) : Qb) := by
  rw [← map_pow, h.2.2.1]
  simp

theorem map_zeta (h : IsLayer (e + 2) q d ζ a b) (φ : L →ₐ[ℚ] Qb) :
    IsPrimitiveRoot (φ ζ) (2 ^ (e + 2)) := h.1.map_of_injective (f := φ) (RingHom.injective φ.toRingHom)

private theorem adjoin_union_eq_sup {E : Type*} [Field E] [Algebra ℚ E] (S T : Set E) :
    adjoin ℚ (S ∪ T) = adjoin ℚ S ⊔ adjoin ℚ T :=
  IntermediateField.gc.l_sup

theorem map_hostE (h : IsLayer (e + 2) q d ζ a b) (φ : L →ₐ[ℚ] Qb) :
    (hostE ζ a b).map φ = EQ e q d := by
  rw [show hostE ζ a b = adjoin ℚ ({a, b} ∪ {ζ + ζ⁻¹}) from (adjoin_union_eq_sup _ _).symm,
    IntermediateField.adjoin_map, Set.image_union, Set.image_insert_eq, Set.image_singleton, Set.image_singleton,
    map_add, map_inv₀, adjoin_union_eq_sup, adjoin_pair_eq_sup]
  show _ = sqQ (-(q : ℤ)) ⊔ sqQ (-(d : ℤ)) ⊔ cycQplus (2 ^ (e + 2))
  rw [sqQ_eq (map_a_sq h φ), sqQ_eq (map_b_sq h φ), cycQplus_eq (map_zeta h φ)]

theorem exists_layer_emb (f : hostE ζ a b →ₐ[ℚ] Qb) :
    ∃ φ : L →ₐ[ℚ] Qb, ∀ x : hostE ζ a b, φ (x : L) = f x := by
  letI : Algebra (hostE ζ a b) Qb := f.toRingHom.toAlgebra
  haveI : FiniteDimensional (hostE ζ a b) L := FiniteDimensional.right ℚ (hostE ζ a b) L
  haveI : Algebra.IsAlgebraic (hostE ζ a b) L := Algebra.IsAlgebraic.of_finite (hostE ζ a b) L
  let ψ : L →ₐ[hostE ζ a b] Qb := IsAlgClosed.lift
  exact ⟨ψ.toRingHom.toRatAlgHom, fun x => ψ.commutes x⟩

theorem range_hostE (h : IsLayer (e + 2) q d ζ a b) (f : hostE ζ a b →ₐ[ℚ] Qb) :
    f.fieldRange = EQ e q d := by
  obtain ⟨φ, hφ⟩ := exists_layer_emb f
  rw [← map_hostE h φ]
  ext y
  simp only [AlgHom.mem_fieldRange, IntermediateField.mem_map]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, hφ x⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, (hφ ⟨x, hx⟩).symm⟩

theorem mem_EQ (h : IsLayer (e + 2) q d ζ a b) (f : hostE ζ a b →ₐ[ℚ] Qb) (x : hostE ζ a b) :
    f x ∈ EQ e q d := by
  rw [← range_hostE h f]
  exact AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩

def jOf (h : IsLayer (e + 2) q d ζ a b) (f : hostE ζ a b →ₐ[ℚ] Qb) : hostE ζ a b ≃ₐ[ℚ] EQ e q d :=
  AlgEquiv.ofBijective (f.codRestrict (EQ e q d).toSubalgebra (mem_EQ h f))
    ⟨fun x y hxy => f.toRingHom.injective (congrArg Subtype.val hxy), fun y => by
      have hy : (y : Qb) ∈ f.fieldRange := by rw [range_hostE h f]; exact y.2
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩⟩

@[simp] theorem jOf_coe (h : IsLayer (e + 2) q d ζ a b) (f : hostE ζ a b →ₐ[ℚ] Qb) (x : hostE ζ a b) :
    ((jOf h f x : EQ e q d) : Qb) = f x := rfl

end Layer

end Formalism.L2.Host
end
end

section
noncomputable section

open IntermediateField NumberField

namespace Formalism.L2.Host

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

theorem mus_mono {M N : ℕ} (h : M ∣ N) : mus M ⊆ mus N := by
  intro z hz
  obtain ⟨c, rfl⟩ := h
  show z ^ (M * c) = 1
  rw [pow_mul, show z ^ M = 1 from hz, one_pow]

theorem cycQ_mono {M N : ℕ} (h : M ∣ N) : cycQ M ≤ cycQ N := adjoin.mono ℚ _ _ (mus_mono h)

theorem cycQplus_le (N : ℕ) : cycQplus N ≤ cycQ N := by
  rw [cycQplus, adjoin_le_iff]
  rintro _ ⟨z, hz, rfl⟩
  have : z ∈ cycQ N := subset_adjoin ℚ _ hz
  exact add_mem this (inv_mem this)

section Gauss

variable (q : ℕ) [Fact q.Prime]

def chiQb : MulChar (ZMod q) Qb := (quadraticChar (ZMod q)).ringHomComp (Int.castRingHom Qb)

def psiQb {w : Qb} (hw : IsPrimitiveRoot w q) : AddChar (ZMod q) Qb := AddChar.zmodChar q hw.pow_eq_one

def gaussQb {w : Qb} (hw : IsPrimitiveRoot w q) : Qb := gaussSum (chiQb q) (psiQb q hw)

variable {q}

theorem gaussQb_mem {w : Qb} (hw : IsPrimitiveRoot w q) : gaussQb q hw ∈ cycQ q := by
  unfold gaussQb gaussSum
  refine sum_mem fun a _ => mul_mem ?_ ?_
  · show ((quadraticChar (ZMod q) a : ℤ) : Qb) ∈ _
    exact intCast_mem _ _
  · show AddChar.zmodChar q hw.pow_eq_one a ∈ _
    rw [AddChar.zmodChar_apply]
    exact pow_mem (subset_adjoin ℚ (mus q) (show w ∈ mus q from hw.pow_eq_one)) _

theorem gaussQb_sq (hq : q % 4 = 3) {w : Qb} (hw : IsPrimitiveRoot w q) :
    gaussQb q hw ^ 2 = ((-(q : ℤ) : ℤ) : Qb) := by
  have hq2 : ringChar (ZMod q) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; rintro rfl; omega
  have hχ₁ : chiQb q ≠ 1 := by
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' hq2
    refine MulChar.ne_one_iff.mpr ⟨a, ?_⟩
    show ((quadraticChar (ZMod q) a : ℤ) : Qb) ≠ 1
    rw [ha]; norm_num
  have hχ₂ : (chiQb q).IsQuadratic := MulChar.IsQuadratic.comp (quadraticChar_isQuadratic (ZMod q)) _
  have hψ : (psiQb q hw).IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root q hw
  have h := gaussSum_sq hχ₁ hχ₂ hψ
  unfold gaussQb
  rw [h, ZMod.card]
  show ((quadraticChar (ZMod q) (-1) : ℤ) : Qb) * _ = _
  rw [quadraticChar_neg_one hq2, ZMod.card, ZMod.χ₄_nat_three_mod_four hq]
  push_cast; ring

theorem sqQ_le_cycQ (hq : q % 4 = 3) : sqQ (-(q : ℤ)) ≤ cycQ q := by
  obtain ⟨w, hw⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Qb q
  rw [sqQ_eq (gaussQb_sq hq hw), adjoin_simple_le_iff]
  exact gaussQb_mem hw

end Gauss

theorem EQ_le_cycQ (e : ℕ) {q d : ℕ} (hq : q.Prime) (hd : d.Prime) (hq4 : q % 4 = 3) (hd4 : d % 4 = 3) :
    EQ e q d ≤ cycQ (condN e q d) := by
  have := Fact.mk hq
  have := Fact.mk hd
  refine sup_le (sup_le ?_ ?_) ?_
  · exact (sqQ_le_cycQ hq4).trans (cycQ_mono (q_dvd_condN e q d))
  · exact (sqQ_le_cycQ hd4).trans (cycQ_mono (d_dvd_condN e q d))
  · exact (cycQplus_le _).trans (cycQ_mono (two_pow_dvd_condN e q d))

end Formalism.L2.Host
end
end

section
noncomputable section

open IntermediateField NumberField

namespace Formalism.HC.HostRaw

open Formalism.FrobeniusOrbits Formalism.L2.Host

variable {φ : Frame} (H : HostRaw φ)

def EQ : Fld := ⨆ j : H.E →ₐ[ℚ] Qb, j.fieldRange

def FI : IntermediateField ℚ H.E := H.F.toIntermediateField fun x => by
  simpa using SubfieldClass.ratCast_mem H.F x

def FQ : Fld := ⨆ j : H.E →ₐ[ℚ] Qb, H.FI.map j

theorem mem_EQ (j : H.E →ₐ[ℚ] Qb) (x : H.E) : j x ∈ H.EQ :=
  (le_iSup (fun j : H.E →ₐ[ℚ] Qb => j.fieldRange) j) ⟨x, rfl⟩

def ActsAs (s : H.EQ →ₐ[ℚ] Qb) (g : φ.GG) : Prop :=
  ∀ (j : H.E →ₐ[ℚ] Qb) (x : H.E), s ⟨j x, H.mem_EQ j x⟩ = j (H.gal.symm g x)

def CondEQ : Prop := IsCond H.EQ H.condN

theorem nonempty_emb : Nonempty (H.E →ₐ[ℚ] Qb) := ⟨IsAlgClosed.lift⟩

theorem exists_aut (j j' : H.E →ₐ[ℚ] Qb) : ∃ σ : H.E ≃ₐ[ℚ] H.E, ∀ x, j' x = j (σ x) := by
  have := H.galois
  have inj : Function.Injective (fun σ : H.E ≃ₐ[ℚ] H.E => j.comp (σ : H.E →ₐ[ℚ] H.E)) := by
    intro σ τ hst
    exact AlgEquiv.ext fun x => j.toRingHom.injective (DFunLike.congr_fun hst x)
  have hb := (Fintype.bijective_iff_injective_and_card _).mpr ⟨inj, by
    rw [AlgHom.card, ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card]⟩
  obtain ⟨σ, hσ⟩ := hb.2 j'
  exact ⟨σ, fun x => (DFunLike.congr_fun hσ x).symm⟩

theorem range_eq (j : H.E →ₐ[ℚ] Qb) : j.fieldRange = H.EQ := by
  refine le_antisymm (le_iSup (fun j : H.E →ₐ[ℚ] Qb => j.fieldRange) j) (iSup_le fun j' => ?_)
  obtain ⟨σ, hσ⟩ := H.exists_aut j j'
  rintro _ ⟨x, rfl⟩
  exact ⟨σ x, (hσ x).symm⟩

theorem aut_mem_F (σ : H.E ≃ₐ[ℚ] H.E) {x : H.E} (hx : x ∈ H.F) : σ x ∈ H.F := fun ψ =>
  hx (ψ.comp (σ : H.E →+* H.E))

theorem map_FI (j : H.E →ₐ[ℚ] Qb) : H.FI.map j = H.FQ := by
  refine le_antisymm (le_iSup (fun j : H.E →ₐ[ℚ] Qb => H.FI.map j) j) (iSup_le fun j' => ?_)
  obtain ⟨σ, hσ⟩ := H.exists_aut j j'
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨σ x, H.aut_mem_F σ hx, (hσ x).symm⟩

theorem mem_F_iff (j : H.E →ₐ[ℚ] Qb) (x : H.E) : x ∈ H.F ↔ j x ∈ H.FQ := by
  rw [← H.map_FI j, IntermediateField.mem_map]
  constructor
  · intro hx; exact ⟨_, hx, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    rwa [← j.toRingHom.injective hxy]

theorem map_K (j : H.E →ₐ[ℚ] Qb) : H.K.map j = KQ H.d := by
  have hb : j H.sqd ^ 2 = ((-(H.d : ℤ) : ℤ) : Qb) := by rw [← map_pow, H.sqd_sq]; simp
  rw [K, adjoin_map, Set.image_singleton, KQ, sqQ_eq hb]

theorem mem_K_iff (j : H.E →ₐ[ℚ] Qb) (x : H.E) : x ∈ H.K ↔ j x ∈ KQ H.d := by
  rw [← H.map_K j, IntermediateField.mem_map]
  constructor
  · intro hx; exact ⟨_, hx, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    rwa [← j.toRingHom.injective hxy]

theorem FQ_le_EQ : H.FQ ≤ H.EQ := iSup_le fun j => by
  rintro _ ⟨x, -, rfl⟩
  exact H.mem_EQ j x

theorem KQ_le_EQ : KQ H.d ≤ H.EQ := by
  obtain ⟨j⟩ := H.nonempty_emb
  rw [← H.map_K j]
  rintro _ ⟨x, -, rfl⟩
  exact H.mem_EQ j x

def jOf (j : H.E →ₐ[ℚ] Qb) : H.E ≃ₐ[ℚ] H.EQ :=
  AlgEquiv.ofBijective (j.codRestrict H.EQ.toSubalgebra (H.mem_EQ j))
    ⟨fun x y hxy => j.toRingHom.injective (congrArg Subtype.val hxy), fun y => by
      have hy : (y : Qb) ∈ j.fieldRange := by rw [H.range_eq j]; exact y.2
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩⟩

@[simp] theorem jOf_coe (j : H.E →ₐ[ℚ] Qb) (x : H.E) : ((H.jOf j x : H.EQ) : Qb) = j x := rfl

instance fin_EQ : FiniteDimensional ℚ H.EQ := by
  obtain ⟨j⟩ := H.nonempty_emb
  exact (H.jOf j).toLinearEquiv.finiteDimensional

instance normal_EQ : Normal ℚ H.EQ := by
  obtain ⟨j⟩ := H.nonempty_emb
  have := H.galois
  exact Normal.of_algEquiv (H.jOf j)

instance fin_FQ : FiniteDimensional ℚ H.FQ :=
  FiniteDimensional.of_injective (inclusion H.FQ_le_EQ).toLinearMap (inclusion H.FQ_le_EQ).toRingHom.injective

theorem FQ_real (τ : Qb →+* ℂ) {y : Qb} (hy : y ∈ H.FQ) : starRingEnd ℂ (τ y) = τ y := by
  obtain ⟨j⟩ := H.nonempty_emb
  rw [← H.map_FI j] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact hx (τ.comp j.toRingHom)

variable {H}

theorem actsAs_of_one {s : H.EQ →ₐ[ℚ] Qb} {g : φ.GG} (j : H.E →ₐ[ℚ] Qb)
    (h : ∀ x : H.E, s ⟨j x, H.mem_EQ j x⟩ = j (H.gal.symm g x)) : H.ActsAs s g := by
  intro j' x
  obtain ⟨σ, hσ⟩ := H.exists_aut j j'
  have h1 : (⟨j' x, H.mem_EQ j' x⟩ : H.EQ) = ⟨j (σ x), H.mem_EQ j _⟩ := Subtype.ext (hσ x)
  rw [h1, h, hσ, ← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, H.gal_comm]

theorem ActsAs.unique {s s' : H.EQ →ₐ[ℚ] Qb} {g : φ.GG} (h : H.ActsAs s g) (h' : H.ActsAs s' g) : s = s' := by
  obtain ⟨j⟩ := H.nonempty_emb
  ext y
  obtain ⟨x, rfl⟩ := (H.jOf j).surjective y
  exact (h j x).trans (h' j x).symm

theorem ActsAs.label_unique {s : H.EQ →ₐ[ℚ] Qb} {g g' : φ.GG} (h : H.ActsAs s g) (h' : H.ActsAs s g') : g = g' := by
  obtain ⟨j⟩ := H.nonempty_emb
  apply H.gal.symm.injective
  ext x
  exact j.toRingHom.injective ((h j x).symm.trans (h' j x))

theorem ActsAs.sqrt_d {s : H.EQ →ₐ[ℚ] Qb} {g : φ.GG} (h : H.ActsAs s g) (x : H.EQ) (hx : (x : Qb) ∈ sqrts (-(H.d : ℤ))) :
    s x = (((g.1.2 : ℤˣ) : ℤ) : Qb) * x := by
  obtain ⟨j⟩ := H.nonempty_emb
  obtain ⟨y, rfl⟩ := (H.jOf j).surjective x
  have hy : y ^ 2 = H.sqd ^ 2 := by
    apply j.toRingHom.injective
    show j (y ^ 2) = j (H.sqd ^ 2)
    rw [H.sqd_sq, map_pow, show j y ^ 2 = ((-(H.d : ℤ) : ℤ) : Qb) from hx]; simp
  have h1 := H.gal_sqd (H.gal.symm g)
  rw [MulEquiv.apply_symm_apply] at h1
  refine (h j y).trans ?_
  rw [jOf_coe]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy with rfl | rfl
  · rw [h1, map_mul, map_intCast]
  · rw [map_neg, h1, map_neg, map_neg, map_mul, map_intCast, mul_neg]

variable (H)

theorem actsAs_gal (j : H.E →ₐ[ℚ] Qb) (σ : H.E ≃ₐ[ℚ] H.E) :
    H.ActsAs ((j.comp (σ : H.E →ₐ[ℚ] H.E)).comp ((H.jOf j).symm : H.EQ →ₐ[ℚ] H.E)) (H.gal σ) := by
  refine actsAs_of_one j fun x => ?_
  show j (σ ((H.jOf j).symm (H.jOf j x))) = _
  rw [AlgEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

theorem adjoin_cycZeta : IntermediateField.adjoin ℚ ({H.cycZeta} : Set (Cond.Cyc H.condN)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have h1 : x ∈ Algebra.adjoin ℚ ({H.cycZeta} : Set (Cond.Cyc H.condN)) := by
    rw [IsCyclotomicExtension.adjoin_primitive_root_eq_top H.cycZeta_prim]; trivial
  exact algebra_adjoin_le_adjoin ℚ _ h1

theorem EQ_le_cycQ : H.EQ ≤ cycQ H.condN := by
  let κ : Cond.Cyc H.condN →ₐ[ℚ] Qb := IsAlgClosed.lift
  have hz : IsPrimitiveRoot (κ H.cycZeta) H.condN := H.cycZeta_prim.map_of_injective κ.toRingHom.injective
  have hκ : κ.fieldRange = cycQ H.condN := by
    rw [AlgHom.fieldRange_eq_map, ← H.adjoin_cycZeta, adjoin_map, Set.image_singleton, cycQ_eq hz]
  rw [← H.range_eq (κ.comp H.cycEmb), ← hκ]
  rintro _ ⟨x, rfl⟩
  exact ⟨H.cycEmb x, rfl⟩

theorem artin (s : Qb ≃ₐ[ℚ] Qb) (u : (ZMod H.condN)ˣ) (hs : ∀ z ∈ mus H.condN, s z = z ^ (u : ZMod H.condN).val) :
    H.ActsAs (restr H.EQ s) (H.art u) := by
  let κ : Cond.Cyc H.condN →ₐ[ℚ] Qb := IsAlgClosed.lift
  obtain ⟨τ, hτ⟩ := Cond.aut H.condN (u : ZMod H.condN).val (ZMod.val_coe_unit_coprime u)
  have hτz := hτ H.cycZeta H.cycZeta_prim.pow_eq_one
  have hcomm : (s : Qb →ₐ[ℚ] Qb).comp κ = κ.comp (τ : Cond.Cyc H.condN →ₐ[ℚ] Cond.Cyc H.condN) := by
    refine AlgHom.ext_of_adjoin_eq_top (s := {H.cycZeta})
      (IsCyclotomicExtension.adjoin_primitive_root_eq_top H.cycZeta_prim) ?_
    rintro _ rfl
    show s (κ H.cycZeta) = κ (τ H.cycZeta)
    rw [hτz, map_pow]
    refine hs _ ?_
    show κ H.cycZeta ^ H.condN = 1
    rw [← map_pow, H.cycZeta_prim.pow_eq_one, map_one]
  refine actsAs_of_one (κ.comp H.cycEmb) fun x => ?_
  show s (κ (H.cycEmb x)) = κ (H.cycEmb (H.gal.symm (H.art u) x))
  rw [H.art_spec u τ hτz x]
  exact DFunLike.congr_fun hcomm (H.cycEmb x)

theorem artin_apply (s : Qb ≃ₐ[ℚ] Qb) (u : (ZMod H.condN)ˣ) (hs : ∀ z ∈ mus H.condN, s z = z ^ (u : ZMod H.condN).val)
    (j : H.E →ₐ[ℚ] Qb) (x : H.E) : s (j x) = j (H.gal.symm (H.art u) x) := H.artin s u hs j x

end Formalism.HC.HostRaw

end
end
