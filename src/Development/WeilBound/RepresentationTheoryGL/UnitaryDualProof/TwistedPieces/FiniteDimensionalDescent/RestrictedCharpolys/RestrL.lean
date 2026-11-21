import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.RestrictedCharpolys.PullPieces
import Mathlib
import GroundTheory.AutomorphicForms.StableConjInvariant
import GroundTheory.LocalFields.Interface
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocalContinuity.LocalDescentHolds
import GroundTheory.AutomorphicForms.ContragredientTranspose.MatrixSimilarity

section
noncomputable section

open ValuativeRel

namespace PositivityTheory.RgUd.TP.Desc.Restr.PfinDim

open PositivityTheory.RgUd.TP.Desc.Restr

theorem finDim (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    FinDim k := by
  intro p c _ _
  letI := frMod (k := k) p c
  letI := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  have hc : CompleteSpace k := inferInstance
  letI : NontriviallyNormedField k := Valued.toNontriviallyNormedField k (ValueGroupWithZero k)
  have : CompleteSpace k := hc
  have : IsTopologicalAddGroup (Fr k p c) := inferInstanceAs (IsTopologicalAddGroup k)
  have : T2Space (Fr k p c) := inferInstanceAs (T2Space k)
  have : LocallyCompactSpace (Fr k p c) := inferInstanceAs (LocallyCompactSpace k)
  have : Nontrivial (Fr k p c) := inferInstanceAs (Nontrivial k)
  have : ContinuousSMul k (Fr k p c) := ⟨by
    show Continuous fun q : k × k => (iterateFrobenius k p c q.1) * q.2
    simp only [iterateFrobenius_def]
    exact (continuous_fst.pow _).mul continuous_snd⟩
  have hfd : FiniteDimensional k (Fr k p c) := FiniteDimensional.of_locallyCompactSpace k
  exact ⟨hfd, Module.finrank_pos⟩

end PositivityTheory.RgUd.TP.Desc.Restr.PfinDim

end
end

section
noncomputable section

open Matrix

namespace PositivityTheory.RgUd.TP.Desc.Restr.PphiA

open PositivityTheory.RgUd.TP.Desc.Restr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

structure FB (k : Type) [Field k] [TopologicalSpace k] (q d : ℕ) where
  β : Fin d → k
  cF : k →+ (Fin d → k)
  recon : ∀ a, ∑ j, cF a j ^ q * β j = a
  uniq : ∀ w : Fin d → k, cF (∑ j, w j ^ q * β j) = w
  cont : Continuous cF

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem fb_smul {q d : ℕ} (B : FB k q d) (l a : k) : B.cF (l ^ q * a) = fun j => l * B.cF a j := by
  conv_lhs => rw [← B.recon a, Finset.mul_sum]
  have : ∑ j, l ^ q * (B.cF a j ^ q * B.β j) = ∑ j, (l * B.cF a j) ^ q * B.β j :=
    Finset.sum_congr rfl fun j _ => by rw [mul_pow]; ring
  rw [this, B.uniq]

theorem fb_exists (hF : FinDim k) (p c : ℕ) [Fact p.Prime] [CharP k p] :
    ∃ d : ℕ, 0 < d ∧ Nonempty (FB k (p ^ c) d) := by
  letI := frMod (k := k) p c
  obtain ⟨hfd, hpos⟩ := hF p c
  set d := Module.finrank k (Fr k p c) with hd
  let b : Module.Basis (Fin d) k (Fr k p c) := Module.finBasis k (Fr k p c)
  let toK : Fr k p c → k := fun x => x
  let ofK : k → Fr k p c := fun x => x
  have hsm : ∀ (a : k) (x : Fr k p c), a • x = ofK (a ^ p ^ c * toK x) := by
    intro a x
    show iterateFrobenius k p c a * toK x = _
    rw [iterateFrobenius_def]
  let β : Fin d → k := fun j => toK (b j)
  let g : (Fin d → k) → k := fun w => ∑ j, w j ^ p ^ c * β j
  have gadd : ∀ v w, g (v + w) = g v + g w := by
    intro v w
    simp only [g, Pi.add_apply, add_pow_char_pow, add_mul, Finset.sum_add_distrib]
  let f : (Fin d → k) →+ k := AddMonoidHom.mk' g gadd
  have hfb : ∀ w, f w = toK (b.equivFun.symm w) := by
    intro w
    rw [Module.Basis.equivFun_symm_apply]
    show ∑ j, w j ^ p ^ c * β j = _
    exact Finset.sum_congr rfl fun j _ => (hsm (w j) (b j)).symm
  have hinj : Function.Injective f := by
    intro v w h
    rw [hfb, hfb] at h
    exact b.equivFun.symm.injective h
  have hsurj : Function.Surjective f := by
    intro a
    refine ⟨b.equivFun (ofK a), ?_⟩
    rw [hfb, LinearEquiv.symm_apply_apply]
  have hcont : Continuous f := by
    show Continuous g
    fun_prop
  have hopen : IsOpenMap f := AddMonoidHom.isOpenMap_of_sigmaCompact f hsurj hcont
  let E : (Fin d → k) ≃+ k := AddEquiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨d, hpos, ⟨{ β := β, cF := E.symm.toAddMonoidHom, recon := ?_, uniq := ?_, cont := ?_ }⟩⟩
  · intro a
    exact E.apply_symm_apply a
  · intro w
    exact E.symm_apply_apply w
  · show Continuous E.symm
    rw [continuous_def]
    intro U hU
    have himg : ⇑E.symm ⁻¹' U = f '' U := by
      ext y
      constructor
      · intro hy
        exact ⟨E.symm y, hy, E.apply_symm_apply y⟩
      · rintro ⟨x, hx, rfl⟩
        show E.symm (E x) ∈ U
        rw [E.symm_apply_apply]
        exact hx
    rw [himg]
    exact hopen U hU

end PositivityTheory.RgUd.TP.Desc.Restr.PphiA
end
end

section
noncomputable section

open Matrix

namespace PositivityTheory.RgUd.TP.Desc.Restr.PphiB

open PositivityTheory.RgUd.TP.Desc.Restr PositivityTheory.RgUd.TP.Desc.Restr.PphiA

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p c d : ℕ} [Fact p.Prime] [CharP k p] (B : FB k (p ^ c) d) {n : ℕ}

abbrev ix (r : Fin (n * d)) : Fin n × Fin d := finProdFinEquiv.symm r

def eF (v : Fin n → k) : Fin (n * d) → k := fun r => B.cF (v (ix r).1) (ix r).2

def eI (w : Fin (n * d) → k) : Fin n → k := fun i => ∑ j, w (finProdFinEquiv (i, j)) ^ p ^ c * B.β j

def φM (x : Matrix (Fin n) (Fin n) k) : Matrix (Fin (n * d)) (Fin (n * d)) k :=
  fun r s => B.cF (x (ix r).1 (ix s).1 * B.β (ix s).2) (ix r).2

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem eI_eF (v : Fin n → k) : eI B (eF B v) = v := by
  funext i
  simp only [eI, eF, ix, Equiv.symm_apply_apply]
  exact B.recon (v i)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem eF_eI (w : Fin (n * d) → k) : eF B (eI B w) = w := by
  funext r
  have h := B.uniq (fun j => w (finProdFinEquiv ((ix r).1, j)))
  simp only [eF, eI]
  rw [h]
  exact congrArg w (finProdFinEquiv.apply_symm_apply r)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem eF_add (v v' : Fin n → k) : eF B (v + v') = eF B v + eF B v' := by
  funext r; simp [eF]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem key (x : Matrix (Fin n) (Fin n) k) (v : Fin n → k) : eF B (x *ᵥ v) = φM B x *ᵥ eF B v := by
  funext r
  simp only [eF, φM, mulVec, dotProduct]
  rw [map_sum, Finset.sum_apply]
  rw [← (finProdFinEquiv : Fin n × Fin d ≃ Fin (n * d)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i' _ => ?_
  simp only [ix, Equiv.symm_apply_apply]
  conv_lhs => rw [← B.recon (v i'), Finset.mul_sum, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [show x (finProdFinEquiv.symm r).1 i' * (B.cF (v i') j' ^ p ^ c * B.β j') =
      B.cF (v i') j' ^ p ^ c * (x (finProdFinEquiv.symm r).1 i' * B.β j') by ring, fb_smul]
  ring

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem eF_surj : Function.Surjective (eF B (n := n)) := fun w => ⟨eI B w, eF_eI B w⟩

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem ext_of_eF {M M' : Matrix (Fin (n * d)) (Fin (n * d)) k} (h : ∀ v, M *ᵥ eF B v = M' *ᵥ eF B v) : M = M' := by
  have hw : ∀ w, M *ᵥ w = M' *ᵥ w := by
    intro w
    obtain ⟨v, rfl⟩ := eF_surj B w
    exact h v
  ext i j
  have h1 := congrFun (hw (Pi.single j 1)) i
  simpa [mulVec_single_one] using h1

def φ : Matrix (Fin n) (Fin n) k →+* Matrix (Fin (n * d)) (Fin (n * d)) k where
  toFun := φM B
  map_one' := ext_of_eF B fun v => by rw [← key, one_mulVec, one_mulVec]
  map_mul' x y := ext_of_eF B fun v => by rw [← key, ← mulVec_mulVec, ← mulVec_mulVec, ← key, ← key, mulVec_mulVec]
  map_zero' := ext_of_eF B fun v => by
    rw [← key, zero_mulVec, zero_mulVec]; funext r; simp [eF]
  map_add' x y := ext_of_eF B fun v => by rw [← key, add_mulVec, add_mulVec, eF_add, key, key]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem φ_apply_mulVec (x : Matrix (Fin n) (Fin n) k) (v : Fin n → k) : φ B x *ᵥ eF B v = eF B (x *ᵥ v) :=
  (key B x v).symm

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem φ_inj : Function.Injective (φ B (n := n)) := by
  intro x y h
  have hv : ∀ v, x *ᵥ v = y *ᵥ v := by
    intro v
    have h1 := φ_apply_mulVec B x v
    rw [h, φ_apply_mulVec] at h1
    have h2 := congrArg (eI B) h1
    rw [eI_eF, eI_eF] at h2
    exact h2.symm
  ext i j
  have h1 := congrFun (hv (Pi.single j 1)) i
  simpa [mulVec_single_one] using h1

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem φ_scal (a : k) : φ B (algebraMap k (Matrix (Fin n) (Fin n) k) (a ^ p ^ c)) = algebraMap k _ a := by
  apply ext_of_eF B
  intro v
  rw [φ_apply_mulVec]
  funext r
  simp [algebraMap_eq_diagonal, mulVec_diagonal, eF, fb_smul]

def e : (Fin n → k) ≃+ (Fin (n * d) → k) where
  toFun := eF B
  invFun := eI B
  left_inv := eI_eF B
  right_inv := eF_eI B
  map_add' := eF_add B

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem continuous_eF : Continuous (eF B (n := n)) := by
  refine continuous_pi fun r => ?_
  exact (continuous_apply _).comp (B.cont.comp (continuous_apply _))

theorem continuous_eI : Continuous (eI B (n := n)) := by
  unfold eI; fun_prop

theorem continuous_φ : Continuous (φ B (n := n)) := by
  show Continuous (φM B)
  unfold φM
  refine continuous_pi fun r => continuous_pi fun s => ?_
  have hx : Continuous fun a : Matrix (Fin n) (Fin n) k => a (ix r).1 (ix s).1 * B.β (ix s).2 := by
    fun_prop
  exact (continuous_apply _).comp (B.cont.comp hx)

def ψ (M : Matrix (Fin (n * d)) (Fin (n * d)) k) : Matrix (Fin n) (Fin n) k :=
  fun i i' => eI B (M *ᵥ eF B (Pi.single i' 1)) i

theorem ψ_φ (x : Matrix (Fin n) (Fin n) k) : ψ B (φ B x) = x := by
  funext i i'
  simp [ψ, φ_apply_mulVec, eI_eF, mulVec_single_one]

theorem continuous_ψ : Continuous (ψ B (n := n)) := by
  unfold ψ
  refine continuous_pi fun i => continuous_pi fun i' => ?_
  exact (continuous_apply i).comp ((continuous_eI B).comp (continuous_id.matrix_mulVec continuous_const))

theorem φ_emb : Topology.IsClosedEmbedding (φ B (n := n)) :=
  Function.LeftInverse.isClosedEmbedding (ψ_φ B) (continuous_ψ B) (continuous_φ B)

end PositivityTheory.RgUd.TP.Desc.Restr.PphiB
end
end

section
noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Restr.PphiC

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Restr PositivityTheory.RgUd.TP.Desc.Restr.PphiA
  PositivityTheory.RgUd.TP.Desc.Restr.PphiB

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p c d : ℕ} [Fact p.Prime] [CharP k p] (B : FB k (p ^ c) d) {n : ℕ}

def Z' (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Subalgebra k (Matrix (Fin (n * d)) (Fin (n * d)) k) :=
  { toSubsemiring := Z.toSubsemiring.map (φ B)
    algebraMap_mem' := fun a => ⟨algebraMap k _ (a ^ p ^ c), Z.algebraMap_mem _, φ_scal B a⟩ }

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem coe_Z' (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) :
    ((Z' B Z : Subalgebra k _) : Set (Matrix (Fin (n * d)) (Fin (n * d)) k)) = φ B '' (Z : Set (Matrix (Fin n) (Fin n) k)) :=
  rfl

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem eI_add (w w' : Fin (n * d) → k) : eI B (w + w') = eI B w + eI B w' := by
  funext i
  simp only [eI, Pi.add_apply, add_pow_char_pow, add_mul, Finset.sum_add_distrib]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

theorem φ_ψ_of_comm (y : Matrix (Fin (n * d)) (Fin (n * d)) k)
    (hy : ∀ b : k, φ B (algebraMap k _ b) * y = y * φ B (algebraMap k _ b)) : φ B (ψ B y) = y := by
  have hsm : ∀ (b : k) (v : Fin n → k), b • v = algebraMap k (Matrix (Fin n) (Fin n) k) b *ᵥ v := by
    intro b v
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
  let L : (Fin n → k) →ₗ[k] (Fin n → k) :=
    { toFun := fun v => eI B (y *ᵥ eF B v)
      map_add' := fun v v' => by
        simp only [eF_add, Matrix.mulVec_add, eI_add]
      map_smul' := fun b v => by
        simp only [RingHom.id_apply]
        rw [hsm b v, hsm b (eI B (y *ᵥ eF B v)), ← φ_apply_mulVec B _ v, Matrix.mulVec_mulVec, ← hy b,
          ← Matrix.mulVec_mulVec]
        conv_lhs => rw [← eF_eI B (y *ᵥ eF B v), φ_apply_mulVec, eI_eF] }
  have hL : ψ B y = LinearMap.toMatrix' L := by
    ext i i'
    rw [LinearMap.toMatrix'_apply]
    rfl
  apply ext_of_eF B
  intro v
  rw [φ_apply_mulVec, hL, LinearMap.toMatrix'_mulVec]
  exact eF_eI B _

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem cen (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Bz (Z' B Z) = φ B '' Bz Z := by
  have mem : ∀ a, a ∈ Z' B Z ↔ ∃ z ∈ Z, φ B z = a := fun a => by
    rw [← SetLike.mem_coe, coe_Z']
    rfl
  ext x
  constructor
  · intro hx
    have hx' : ∀ a ∈ Z' B Z, a * x = x * a := hx
    have hsc : ∀ b : k, φ B (algebraMap k _ b) * x = x * φ B (algebraMap k _ b) := fun b =>
      hx' _ ((mem _).2 ⟨_, Z.algebraMap_mem b, rfl⟩)
    refine ⟨ψ B x, ?_, φ_ψ_of_comm B x hsc⟩
    show ∀ a ∈ Z, a * ψ B x = ψ B x * a
    intro z hz
    apply φ_inj B
    rw [map_mul, map_mul, φ_ψ_of_comm B x hsc]
    exact hx' _ ((mem _).2 ⟨z, hz, rfl⟩)
  · rintro ⟨y, hy, rfl⟩
    have hy' : ∀ a ∈ Z, a * y = y * a := hy
    show ∀ a ∈ Z' B Z, a * φ B y = φ B y * a
    intro a ha
    obtain ⟨z, hz, rfl⟩ := (mem a).1 ha
    rw [← map_mul, ← map_mul, hy' z hz]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem gz (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (g' : GL (Fin (n * d)) k) :
    g' ∈ Gz (Z' B Z) ↔ ∃ g ∈ Gz Z, φ B g.val = g'.val := by
  constructor
  · intro hg
    have hg' : ∀ a ∈ Z' B Z, a * g'.val = g'.val * a := hg
    have h1 : g'.val ∈ φ B '' Bz Z := by
      rw [← cen]
      exact hg
    have h2 : (g'⁻¹).val ∈ φ B '' Bz Z := by
      rw [← cen]
      show ∀ a ∈ Z' B Z, a * (g'⁻¹).val = (g'⁻¹).val * a
      intro a ha
      have e := congrArg (fun m => (g'⁻¹).val * m * (g'⁻¹).val) (hg' a ha)
      simp only [mul_assoc, Units.mul_inv, mul_one, Units.inv_mul_cancel_left] at e
      exact e.symm
    obtain ⟨y, hy, hyg⟩ := h1
    obtain ⟨y', hy', hyg'⟩ := h2
    have e1 : y * y' = 1 := φ_inj B (by rw [map_mul, map_one, hyg, hyg', Units.mul_inv])
    have e2 : y' * y = 1 := φ_inj B (by rw [map_mul, map_one, hyg, hyg', Units.inv_mul])
    exact ⟨⟨y, y', e1, e2⟩, hy, hyg⟩
  · rintro ⟨g, hg, hgg⟩
    have h : g'.val ∈ Bz (Z' B Z) := by
      rw [cen]
      exact ⟨g.val, hg, hgg⟩
    exact h

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem cr (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) : CR (Z' B Z) := by
  obtain ⟨hc, hr⟩ := hZ
  have mem : ∀ a, a ∈ Z' B Z ↔ ∃ z ∈ Z, φ B z = a := fun a => by
    rw [← SetLike.mem_coe, coe_Z']
    rfl
  refine ⟨?_, ⟨?_⟩⟩
  · intro a ha b hb
    obtain ⟨z, hz, rfl⟩ := (mem a).1 ha
    obtain ⟨w, hw, rfl⟩ := (mem b).1 hb
    rw [← map_mul, ← map_mul, hc z hz w hw]
  · rintro ⟨x, hx⟩ ⟨m, hm⟩
    obtain ⟨z, hz, rfl⟩ := (mem x).1 hx
    have hzm : (⟨z, hz⟩ : Z) ^ m = 0 := by
      apply Subtype.ext
      apply φ_inj B
      have := congrArg Subtype.val hm
      simpa [map_pow] using this
    have h0 := hr.eq_zero _ ⟨m, hzm⟩
    have hz0 : z = 0 := congrArg Subtype.val h0
    apply Subtype.ext
    simp [hz0]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem roots (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : HasRoots (Z' B Z) (p ^ c) := fun a =>
  ⟨φ B (algebraMap k _ a), ⟨_, Z.algebraMap_mem a, rfl⟩, by rw [← map_pow, ← map_pow, φ_scal]⟩

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [TopologicalSpace k] in
theorem pow_card_eq_zero (x : Matrix (Fin n) (Fin n) k) (hx : IsNilpotent x) : x ^ n = 0 := by
  have h := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hx
  have h2 : x.charpoly = X ^ Fintype.card (Fin n) := sub_eq_zero.1 h.eq_zero
  have h3 := Matrix.aeval_self_charpoly x
  rw [h2, map_pow, aeval_X, Fintype.card_fin] at h3
  exact h3

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem nil (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hn : n ≤ p ^ c) : NilBound (Z' B Z) (p ^ c) := by
  intro y hy hnil
  rw [cen] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hxn : IsNilpotent x := by
    obtain ⟨m, hm⟩ := hnil
    exact ⟨m, φ_inj B (by rw [map_pow, hm, map_zero])⟩
  rw [← map_pow, pow_eq_zero_of_le hn (pow_card_eq_zero x hxn), map_zero]

end PositivityTheory.RgUd.TP.Desc.Restr.PphiC
end
end

section
noncomputable section

open Matrix

namespace PositivityTheory.RgUd.TP.Desc.Restr.PphiD

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Restr PositivityTheory.RgUd.TP.Desc.Restr.PphiA
  PositivityTheory.RgUd.TP.Desc.Restr.PphiB PositivityTheory.RgUd.TP.Desc.Restr.PphiC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p c d : ℕ} [Fact p.Prime] [CharP k p] (B : FB k (p ^ c) d) {n : ℕ}

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
include B in
theorem d_pos : 0 < d := by
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h
    have := B.recon 1
    simp at this
  · exact h

def img (S : Submodule k (Matrix (Fin n) (Fin n) k)) : Submodule k (Matrix (Fin (n * d)) (Fin (n * d)) k) where
  carrier := φ B '' (S : Set (Matrix (Fin n) (Fin n) k))
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, S.add_mem ha hb, map_add _ _ _⟩
  zero_mem' := ⟨0, S.zero_mem, map_zero _⟩
  smul_mem' := by
    rintro l _ ⟨a, ha, rfl⟩
    refine ⟨(l ^ p ^ c) • a, S.smul_mem _ ha, ?_⟩
    rw [Algebra.smul_def, map_mul, φ_scal, ← Algebra.smul_def]

def coefF {m : ℕ} (w : Fin m × Fin d → k) : Fin m → k := fun l => ∑ j, w (l, j) ^ p ^ c * B.β j

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem coefF_add {m : ℕ} (w w' : Fin m × Fin d → k) : coefF B (w + w') = coefF B w + coefF B w' := by
  funext l; simp only [coefF, Pi.add_apply, add_pow_char_pow, add_mul, Finset.sum_add_distrib]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem coefF_smul {m : ℕ} (l : k) (w : Fin m × Fin d → k) : coefF B (l • w) = (l ^ p ^ c) • coefF B w := by
  funext l
  simp only [coefF, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum, mul_assoc]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem coefF_cF {m : ℕ} (x : Fin m → k) : coefF B (fun lj => B.cF (x lj.1) lj.2) = x := by
  funext l; exact B.recon (x l)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fact p.Prime] [CharP k p] in
theorem coefF_inj {m : ℕ} {w w' : Fin m × Fin d → k} (h : coefF B w = coefF B w') : w = w' := by
  funext x
  obtain ⟨l, j⟩ := x
  have h1 : (fun j => w (l, j)) = fun j => w' (l, j) := by
    rw [← B.uniq (fun j => w (l, j)), ← B.uniq (fun j => w' (l, j))]
    exact congrArg B.cF (congrFun h l)
  exact congrFun h1 j

def Lmap (S : Submodule k (Matrix (Fin n) (Fin n) k)) :
    (Fin (Module.finrank k S) × Fin d → k) →ₗ[k] img B S where
  toFun w := ⟨φ B ((Module.finBasis k S).equivFun.symm (coefF B w) : Matrix (Fin n) (Fin n) k),
    ⟨_, ((Module.finBasis k S).equivFun.symm (coefF B w)).2, rfl⟩⟩
  map_add' w w' := by
    apply Subtype.ext
    simp only [coefF_add, map_add, Submodule.coe_add]
  map_smul' l w := by
    apply Subtype.ext
    simp only [coefF_smul, map_smul, SetLike.val_smul, RingHom.id_apply]
    rw [Algebra.smul_def, map_mul, φ_scal, ← Algebra.smul_def]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem Lmap_bij (S : Submodule k (Matrix (Fin n) (Fin n) k)) : Function.Bijective (Lmap B S) := by
  constructor
  · intro w w' h
    have h1 := φ_inj B (congrArg Subtype.val h)
    exact coefF_inj B ((Module.finBasis k S).equivFun.symm.injective (Subtype.ext h1))
  · rintro ⟨_, ⟨s, hs, rfl⟩⟩
    refine ⟨fun lj => B.cF ((Module.finBasis k S).equivFun ⟨s, hs⟩ lj.1) lj.2, Subtype.ext ?_⟩
    have e1 : (Module.finBasis k S).equivFun.symm (coefF B fun lj => B.cF ((Module.finBasis k S).equivFun ⟨s, hs⟩ lj.1) lj.2)
        = ⟨s, hs⟩ := by
      rw [coefF_cF, LinearEquiv.symm_apply_apply]
    exact congrArg (fun t : S => φ B (t : Matrix (Fin n) (Fin n) k)) e1

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem finrank_img (S : Submodule k (Matrix (Fin n) (Fin n) k)) :
    Module.finrank k (img B S) = d * Module.finrank k S := by
  have e := (LinearEquiv.ofBijective (Lmap B S) (Lmap_bij B S)).finrank_eq
  rw [← e, Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, mul_comm]

end PositivityTheory.RgUd.TP.Desc.Restr.PphiD
end
end

section
noncomputable section

open Matrix

namespace PositivityTheory.RgUd.TP.Desc.Restr.PphiE

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Restr PositivityTheory.RgUd.TP.Desc.Restr.PphiA
  PositivityTheory.RgUd.TP.Desc.Restr.PphiB PositivityTheory.RgUd.TP.Desc.Restr.PphiC PositivityTheory.RgUd.TP.Desc.Restr.PphiD

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p c d : ℕ} [Fact p.Prime] [CharP k p] (B : FB k (p ^ c) d) {n : ℕ}

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem primIdem_Z' (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : primIdem (Z' B Z) = φ B '' primIdem Z := by
  have hinj := φ_inj B (n := n)
  have hZ : ∀ x, x ∈ Z' B Z ↔ ∃ y ∈ Z, φ B y = x := fun x => by
    rw [← SetLike.mem_coe, coe_Z', Set.mem_image]
    simp only [SetLike.mem_coe]
  have hidem : ∀ x : Matrix (Fin n) (Fin n) k, IsIdempotentElem (φ B x) ↔ IsIdempotentElem x := fun x => by
    show φ B x * φ B x = φ B x ↔ x * x = x
    rw [← map_mul]
    exact hinj.eq_iff
  ext e'
  constructor
  · rintro ⟨he'Z, hid, hne, hmin⟩
    obtain ⟨e, heZ, rfl⟩ := (hZ e').1 he'Z
    refine ⟨e, ⟨heZ, (hidem e).1 hid, fun h => hne (by rw [h, map_zero]), fun f hfZ hf hfe => ?_⟩, rfl⟩
    rcases hmin (φ B f) ((hZ _).2 ⟨f, hfZ, rfl⟩) ((hidem f).2 hf) (by rw [← map_mul, hfe]) with h | h
    · left
      exact hinj (by rw [h, map_zero])
    · right
      exact hinj h
  · rintro ⟨e, ⟨heZ, hid, hne, hmin⟩, rfl⟩
    refine ⟨(hZ _).2 ⟨e, heZ, rfl⟩, (hidem e).2 hid, fun h => hne (hinj (by rw [h, map_zero])),
      fun f' hf'Z hf' hfe => ?_⟩
    obtain ⟨f, hfZ, rfl⟩ := (hZ f').1 hf'Z
    rcases hmin f hfZ ((hidem f).1 hf') (hinj (by rw [map_mul, hfe])) with h | h
    · left
      rw [h, map_zero]
    · right
      rw [h]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem cen_map (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (e : Matrix (Fin n) (Fin n) k) :
    (cenSub (Z' B Z)).map (LinearMap.mulLeft k (φ B e)) = img B ((cenSub Z).map (LinearMap.mulLeft k e)) := by
  have hc : ∀ {m : ℕ} (W : Subalgebra k (Matrix (Fin m) (Fin m) k)) (x : Matrix (Fin m) (Fin m) k),
      x ∈ cenSub W ↔ x ∈ Bz W := fun W x => Iff.rfl
  have hcen := cen B Z
  ext y
  constructor
  · rintro ⟨x', hx', rfl⟩
    have h1 : x' ∈ φ B '' Bz Z := by
      rw [← hcen]
      exact (hc _ _).1 hx'
    obtain ⟨x, hx, rfl⟩ := h1
    exact ⟨e * x, ⟨x, (hc _ _).2 hx, rfl⟩, by
      show φ B (e * x) = φ B e * φ B x
      exact map_mul _ _ _⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have h1 : φ B x ∈ Bz (Z' B Z) := by
      rw [hcen]
      exact ⟨x, (hc _ _).1 hx, rfl⟩
    exact ⟨φ B x, (hc _ _).2 h1, by
      show φ B e * φ B x = φ B (e * x)
      exact (map_mul _ _ _).symm⟩

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem z_map (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (e : Matrix (Fin n) (Fin n) k) :
    (Z' B Z).toSubmodule.map (LinearMap.mulLeft k (φ B e)) = img B (Z.toSubmodule.map (LinearMap.mulLeft k e)) := by
  have hZ : ∀ x, x ∈ Z' B Z ↔ ∃ y ∈ Z, φ B y = x := fun x => by
    rw [← SetLike.mem_coe, coe_Z', Set.mem_image]
    simp only [SetLike.mem_coe]
  ext y
  constructor
  · rintro ⟨x', hx', rfl⟩
    obtain ⟨x, hx, rfl⟩ := (hZ x').1 hx'
    exact ⟨e * x, ⟨x, hx, rfl⟩, by
      show φ B (e * x) = φ B e * φ B x
      exact map_mul _ _ _⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨φ B x, (hZ _).2 ⟨x, hx, rfl⟩, by
      show φ B e * φ B x = φ B (e * x)
      exact (map_mul _ _ _).symm⟩

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem mu_Z' (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : mu (Z' B Z) = mu Z := by
  unfold mu
  rw [primIdem_Z', finsum_mem_image (fun x _ y _ h => φ_inj B h)]
  refine finsum_mem_congr rfl fun e _ => ?_
  rw [cen_map, z_map, finrank_img, finrank_img]
  exact Nat.mul_div_mul_left _ _ (d_pos B)

end PositivityTheory.RgUd.TP.Desc.Restr.PphiE
end
end

section
namespace PositivityTheory.RgUd.TP.Desc.Restr.Pphi1

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Restr PositivityTheory.RgUd.TP.Desc.Restr.PphiA
  PositivityTheory.RgUd.TP.Desc.Restr.PphiB PositivityTheory.RgUd.TP.Desc.Restr.PphiC PositivityTheory.RgUd.TP.Desc.Restr.PphiE

theorem phiEx (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    FinDim k → PhiEx k := by
  intro hF p c _ _ n Z hZ hn
  obtain ⟨d, -, ⟨B⟩⟩ := fb_exists hF p c
  exact ⟨n * d, Z' B Z, φ B, e B,
    { inj := φ_inj B
      emb := φ_emb B
      econt := continuous_eF B
      econt' := continuous_eI B
      intertw := fun x v => key B x v
      carrier := coe_Z' B Z
      cen := cen B Z
      gz := gz B Z
      scal := φ_scal B
      cr := cr B Z hZ
      mu := mu_Z' B Z
      roots := roots B Z
      nil := nil B Z hn }⟩

end PositivityTheory.RgUd.TP.Desc.Restr.Pphi1
end

section
noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Restr.Ppull2A

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Restr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n N q : ℕ} {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {Z' : Subalgebra k (Matrix (Fin N) (Fin N) k)}
  {φ : Matrix (Fin n) (Fin n) k →+* Matrix (Fin N) (Fin N) k} {e : (Fin n → k) ≃+ (Fin N → k)}

theorem choose_zero (hd : PhiData q Z Z' φ e) (hN : 0 < N) :
    1 ≤ q ∧ ∀ i, 0 < i → i < q → (q.choose i : k) = 0 := by
  have hinf : Infinite k := by
    obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := ValuativeRel.valuation k)
    by_contra hfin
    rw [not_infinite_iff_finite] at hfin
    classical
    haveI := Fintype.ofFinite k
    have hr : r ≠ 0 := by simpa using hr0
    have h1 := FiniteField.pow_card_sub_one_eq_one r hr
    have h2 := congrArg (ValuativeRel.valuation k) h1
    rw [map_pow, map_one] at h2
    have hc : Fintype.card k - 1 ≠ 0 := by
      have := Fintype.one_lt_card (α := k)
      omega
    exact (pow_lt_one₀ zero_le' hr1 hc).ne h2
  haveI : Nontrivial (Matrix (Fin N) (Fin N) k) := by
    haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    infer_instance
  let f : k →+* Matrix (Fin N) (Fin N) k := φ.comp (algebraMap k _)
  have hfinj : Function.Injective f := f.injective
  have hfq : ∀ a : k, f (a ^ q) = algebraMap k _ a := fun a => hd.scal a
  have hq : 1 ≤ q := by
    by_contra h
    have h0 : q = 0 := by omega
    have h3 := hfq 0
    rw [h0, pow_zero, map_one, map_zero] at h3
    exact one_ne_zero h3
  have hadd : ∀ a b : k, (a + b) ^ q = a ^ q + b ^ q := by
    intro a b
    apply hfinj
    rw [hfq, map_add, map_add, hfq, hfq]
  refine ⟨hq, fun i hi1 hi2 => ?_⟩
  have hP : ((X + 1 : k[X]) ^ q - X ^ q - 1) = 0 := by
    apply Polynomial.funext
    intro a
    simp [hadd a 1]
  have h4 := congrArg (fun p => p.coeff i) hP
  have hi0 : i ≠ 0 := by omega
  have hiq : i ≠ q := by omega
  simpa [coeff_X_add_one_pow, coeff_X_pow, coeff_one, hi0, hiq, Ne.symm hi0] using h4

theorem pow_sum {R : Type*} [Ring R] {q : ℕ} (hq : 1 ≤ q) (hc : ∀ i, 0 < i → i < q → (q.choose i : R) = 0)
    {ι : Type*} (s : Finset ι) (a : ι → R) (hcomm : ∀ i j, Commute (a i) (a j)) :
    (∑ i ∈ s, a i) ^ q = ∑ i ∈ s, a i ^ q := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, zero_pow (by omega)]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, ← ih]
    have hc' : Commute (a j) (∑ i ∈ s, a i) := Commute.sum_right _ _ _ fun i _ => hcomm j i
    rw [hc'.add_pow, Finset.sum_eq_add q 0 (by omega)]
    · simp
    · intro m hm hm'
      rw [hc m (by omega) (by have := Finset.mem_range.1 hm; omega), mul_zero]
    · intro h
      simp at h
    · intro h
      simp at h

theorem aeval_expand (hd : PhiData q Z Z' φ e) (hN : 0 < N) (χ : k[X]) (x : Matrix (Fin n) (Fin n) k)
    (hx : aeval x χ = 0) : aeval (φ x) (expand k q χ) = 0 := by
  obtain ⟨hq, hc⟩ := choose_zero hd hN
  have hcM : ∀ i, 0 < i → i < q → (q.choose i : Matrix (Fin N) (Fin N) k) = 0 := by
    intro i h1 h2
    rw [← map_natCast (algebraMap k (Matrix (Fin N) (Fin N) k)), hc i h1 h2, map_zero]
  have hsum : φ (aeval x χ) = ∑ i ∈ Finset.range (χ.natDegree + 1), φ (χ.coeff i • x ^ i) := by
    rw [aeval_eq_sum_range, map_sum]
  rw [hx, map_zero] at hsum
  have hp := pow_sum hq hcM (Finset.range (χ.natDegree + 1)) (fun i => φ (χ.coeff i • x ^ i))
    (fun i j => (((Commute.pow_pow_self x i j).smul_left _).smul_right _).map φ)
  beta_reduce at hp
  rw [← hsum, zero_pow (by omega)] at hp
  rw [expand_aeval, aeval_eq_sum_range, hp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_pow φ (χ.coeff i • x ^ i) q, _root_.smul_pow, ← pow_mul, ← pow_mul, Algebra.smul_def,
    Algebra.smul_def, map_mul, hd.scal, map_pow, mul_comm q i]

private theorem sub_dvd_lemma {R : Type*} [Ring R] [Algebra k R] (P : k[X]) (x y : R) (h : Commute x y) :
    ∃ Q : R, aeval x P - aeval y P = Q * (x - y) := by
  refine ⟨∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i • ∑ j ∈ Finset.range i, x ^ j * y ^ (i - 1 - j), ?_⟩
  rw [aeval_eq_sum_range, aeval_eq_sum_range, ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← smul_sub, smul_mul_assoc, h.geom_sum₂_mul]

theorem finite_charpoly (N : ℕ) (P : k[X]) (hP : P ≠ 0) :
    ∃ l : List k[X], l.Nodup ∧ ∀ A : Matrix (Fin N) (Fin N) k, aeval A P = 0 → A.charpoly ∈ l := by
  classical
  let F := Polynomial.fintypeSubtypeMonicDvd (P ^ N) (pow_ne_zero N hP)
  refine ⟨((@Finset.univ _ F).image Subtype.val).toList, Finset.nodup_toList _, fun A hA => ?_⟩
  rw [Finset.mem_toList, Finset.mem_image]
  refine ⟨⟨A.charpoly, A.charpoly_monic, ?_⟩, Finset.mem_univ _, rfl⟩
  let ψ := (Algebra.ofId k k[X]).mapMatrix (m := Fin N)
  let T : Matrix (Fin N) (Fin N) k[X] := algebraMap k[X] _ X
  obtain ⟨Q, hQ⟩ := sub_dvd_lemma P T (ψ A) (Algebra.commute_algebraMap_left X (ψ A))
  have h1 : aeval (ψ A) P = 0 := by rw [aeval_algHom_apply, hA, map_zero]
  have h2 : aeval T P = algebraMap k[X] _ P := by
    rw [aeval_algebraMap_apply, aeval_X_left_apply]
  have h3 : T - ψ A = charmatrix A := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [T, ψ, charmatrix_apply, Matrix.algebraMap_matrix_apply]
    · simp [T, ψ, charmatrix_apply, Matrix.algebraMap_matrix_apply, hij]
  rw [h1, h2, sub_zero, h3] at hQ
  have h4 := congrArg Matrix.det hQ
  rw [det_mul, Matrix.algebraMap_eq_diagonal] at h4
  simp only [det_diagonal] at h4
  simp at h4
  exact ⟨Q.det, by rw [h4, mul_comm]; rfl⟩

end PositivityTheory.RgUd.TP.Desc.Restr.Ppull2A
end
end

section
noncomputable section

open Matrix GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker Set Topology

namespace PositivityTheory.RgUd.TP.Desc.Restr.Ppull2B

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Restr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n N q : ℕ} {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {Z' : Subalgebra k (Matrix (Fin N) (Fin N) k)}
  {φ : Matrix (Fin n) (Fin n) k →+* Matrix (Fin N) (Fin N) k} {e : (Fin n → k) ≃+ (Fin N → k)}

def Φ (φ : Matrix (Fin n) (Fin n) k →+* Matrix (Fin N) (Fin N) k) (e : (Fin n → k) ≃+ (Fin N → k)) (p : Sp k n) : Sp k N :=
  (φ p.1, e p.2)

def eH (hd : PhiData q Z Z' φ e) : (Fin n → k) ≃ₜ (Fin N → k) :=
  { toEquiv := e.toEquiv, continuous_toFun := hd.econt, continuous_invFun := hd.econt' }

theorem isClosedEmbedding_Φ (hd : PhiData q Z Z' φ e) : IsClosedEmbedding (Φ φ e) :=
  hd.emb.prodMap (eH hd).isClosedEmbedding

theorem comp_mem (hd : PhiData q Z Z' φ e) {f : Sp k N → ℂ} (hf : f ∈ locallyConstantCompactSupport (Sp k N) ℂ ℂ) :
    f ∘ Φ φ e ∈ locallyConstantCompactSupport (Sp k n) ℂ ℂ := by
  obtain ⟨h1, h2⟩ := hf
  exact ⟨h1.comp_continuous (isClosedEmbedding_Φ hd).continuous,
    h2.comp_isClosedEmbedding (isClosedEmbedding_Φ hd)⟩

theorem inv_val (hd : PhiData q Z Z' φ e) {g : GL (Fin n) k} {g' : GL (Fin N) k} (h : φ g.val = g'.val) :
    φ g⁻¹.val = g'⁻¹.val := by
  calc φ g⁻¹.val = φ g⁻¹.val * (g'.val * g'⁻¹.val) := by simp
    _ = φ (g⁻¹.val * g.val) * g'⁻¹.val := by rw [map_mul, h, mul_assoc]
    _ = g'⁻¹.val := by simp

theorem act_Φ (hd : PhiData q Z Z' φ e) {g : GL (Fin n) k} {g' : GL (Fin N) k} (h : φ g.val = g'.val) (p : Sp k n) :
    act g' (Φ φ e p) = Φ φ e (act g p) := by
  simp only [act, Φ, map_mul, hd.intertw, h, inv_val hd h]

private theorem exists_compact_clopen_between {Y : Type*} [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    [TotallyDisconnectedSpace Y] {K U : Set Y} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ V : Set Y, IsClopen V ∧ IsCompact V ∧ K ⊆ V ∧ V ⊆ U := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  have hb := loc_compact_Haus_tot_disc_of_zero_dim (H := Y)
  have hx : ∀ x : K, ∃ V : Set Y, IsClopen V ∧ (x : Y) ∈ V ∧ V ⊆ interior L := fun x =>
    hb.mem_nhds_iff.1 (isOpen_interior.mem_nhds (hKL x.2))
  choose V hV using hx
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover V (fun x => (hV x).1.isOpen)
    (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, (hV ⟨x, hx⟩).2.1⟩)
  have hcl : IsClopen (⋃ i ∈ I, V i) := I.finite_toSet.isClopen_biUnion (fun i _ => (hV i).1)
  refine ⟨⋃ i ∈ I, V i, hcl, ?_, hI, ?_⟩
  · exact hL.of_isClosed_subset hcl.isClosed
      (iUnion₂_subset fun i _ => (hV i).2.2.trans interior_subset)
  · exact iUnion₂_subset fun i _ => (hV i).2.2.trans (interior_subset.trans hLU)

private theorem exists_compact_clopen_preimage_Phi_eq (hd : PhiData q Z Z' φ e) {A : Set (Sp k n)} (hA : IsClopen A)
    (hAc : IsCompact A) (hAO : A ⊆ {p | p.2 ≠ 0}) :
    ∃ B : Set (Sp k N), IsClopen B ∧ IsCompact B ∧ B ⊆ {p | p.2 ≠ 0} ∧ Φ φ e ⁻¹' B = A := by
  haveI := totallyDisconnectedSpace_localField (F := k)
  haveI : TotallyDisconnectedSpace (Matrix (Fin N) (Fin N) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin N → Fin N → k))
  have hE := isClosedEmbedding_Φ hd
  have hO : IsOpen ({p : Sp k N | p.2 ≠ 0} ∩ (Φ φ e '' Aᶜ)ᶜ) :=
    (isOpen_ne_fun continuous_snd continuous_const).inter
      (hE.isClosedMap _ hA.isOpen.isClosed_compl).isOpen_compl
  have hKO : Φ φ e '' A ⊆ {p : Sp k N | p.2 ≠ 0} ∩ (Φ φ e '' Aᶜ)ᶜ := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · show e x.2 ≠ 0
      intro h0
      exact hAO hx ((map_eq_zero_iff e e.injective).1 h0)
    · rintro ⟨y, hy, hyx⟩
      exact hy (hE.injective hyx ▸ hx)
  obtain ⟨V, hV, hVc, hKV, hVO⟩ :=
    exists_compact_clopen_between (Y := Sp k N) (hAc.image hE.continuous) hO hKO
  refine ⟨V, hV, hVc, fun p hp => (hVO hp).1, ?_⟩
  ext x
  constructor
  · intro hx
    by_contra hxA
    exact (hVO hx).2 ⟨x, hxA, rfl⟩
  · intro hx
    exact hKV ⟨x, hx, rfl⟩

private theorem exists_supportedIn_comp_Phi_eq (hd : PhiData q Z Z' φ e) {f : Sp k n → ℂ}
    (hf : f ∈ supportedIn {p : Sp k n | p.2 ≠ 0}) :
    ∃ h ∈ supportedIn {p : Sp k N | p.2 ≠ 0}, h ∘ Φ φ e = f := by
  obtain ⟨⟨hlc, hcs⟩, hsupp⟩ := hf
  have hK := hcs.isCompact
  have key : ∀ c : ℂ, c ≠ 0 → ∃ B : Set (Sp k N), IsClopen B ∧ IsCompact B ∧
      B ⊆ {p | p.2 ≠ 0} ∧ Φ φ e ⁻¹' B = f ⁻¹' {c} := by
    intro c hc
    have hcl : IsClopen (f ⁻¹' {c}) := hlc.isClopen_fiber c
    have hsub : f ⁻¹' {c} ⊆ Function.support f := fun x hx => by
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
      simp [Function.mem_support, hx, hc]
    exact exists_compact_clopen_preimage_Phi_eq hd hcl
      (hK.of_isClosed_subset hcl.isClosed (hsub.trans (subset_tsupport f))) (hsub.trans hsupp)
  choose! B hB using key
  have hfin : (Set.range f).Finite := by
    haveI : CompactSpace (tsupport f) := isCompact_iff_compactSpace.1 hK
    have hc : Continuous (fun x : tsupport f => (x : Sp k n)) := continuous_subtype_val
    have h1 := (hlc.comp_continuous hc).range_finite
    refine (h1.insert 0).subset ?_
    rintro _ ⟨x, rfl⟩
    by_cases hx : f x = 0
    · exact Or.inl hx
    · exact Or.inr ⟨⟨x, subset_tsupport f hx⟩, rfl⟩
  set S := hfin.toFinset.filter (· ≠ 0) with hS
  refine ⟨∑ c ∈ S, c • (B c).indicator (fun _ => (1 : ℂ)), ?_, ?_⟩
  · refine Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ ?_
    have hc0 : c ≠ 0 := (Finset.mem_filter.1 hc).2
    obtain ⟨hBc, hBk, hBO, -⟩ := hB c hc0
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro s
      have := Set.indicator_const_preimage (B c) s (1 : ℂ)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
      rcases this with h | h | h | h <;> rw [h]
      exacts [isOpen_univ, hBc.isOpen, hBc.isClosed.isOpen_compl, isOpen_empty]
    · exact HasCompactSupport.intro hBk fun x hx => Set.indicator_of_notMem hx _
    · exact Set.support_indicator_subset.trans hBO
  · funext x
    simp only [Function.comp_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hterm : ∀ c ∈ S, c * (B c).indicator (fun _ => (1 : ℂ)) (Φ φ e x) =
        if f x = c then c else 0 := by
      intro c hc
      have hpre := (hB c (Finset.mem_filter.1 hc).2).2.2.2
      by_cases hx : f x = c
      · have hm : Φ φ e x ∈ B c := by
          show x ∈ Φ φ e ⁻¹' B c
          rw [hpre]
          exact hx
        simp [Set.indicator_of_mem hm, hx]
      · have hm : Φ φ e x ∉ B c := by
          show x ∉ Φ φ e ⁻¹' B c
          rw [hpre]
          exact hx
        simp [Set.indicator_of_notMem hm, hx]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · by_contra hne
      exact h (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ⟨x, rfl⟩, Ne.symm hne⟩)

theorem fibVan_pull (hd : PhiData q Z Z' φ e) (F : Set (Matrix (Fin n) (Fin n) k))
    (F' : Set (Matrix (Fin N) (Fin N) k)) (hF : ∀ x ∈ F, φ x ∈ F') (h' : FibVan Z' F') : FibVan Z F := by
  intro ξ hS hI
  let ξ' : (Sp k N → ℂ) →ₗ[ℂ] ℂ := ξ.comp (LinearMap.funLeft ℂ ℂ (Φ φ e))
  have hmem : ∀ g ∈ supportedIn (univ : Set (Sp k N)),
      g ∘ Φ φ e ∈ supportedIn (univ : Set (Sp k n)) := by
    intro g hg
    obtain ⟨hg1, -⟩ := hg
    exact ⟨comp_mem hd hg1, subset_univ _⟩
  have hS' : Supp ξ' (F' ×ˢ univ) := by
    intro g hg hz
    show ξ (g ∘ Φ φ e) = 0
    refine hS _ (hmem g hg) ?_
    rintro p ⟨hp, -⟩
    exact hz _ ⟨hF _ hp, mem_univ _⟩
  have hI' : PositivityTheory.RgUd.T.Inv Z' ξ' := by
    intro g' hg' g hg
    obtain ⟨g0, hg0, hφ⟩ := (hd.gz g').1 hg'
    show ξ ((fun p => g (act g' p)) ∘ Φ φ e) = ξ (g ∘ Φ φ e)
    have hfun : ((fun p => g (act g' p)) ∘ Φ φ e) = fun p => (g ∘ Φ φ e) (act g0 p) := by
      funext p
      simp only [Function.comp_apply, act_Φ hd hφ]
    rw [hfun]
    exact hI g0 hg0 _ (hmem g hg)
  have hK := h' ξ' hS' hI'
  intro f hf
  obtain ⟨h, hh, rfl⟩ := exists_supportedIn_comp_Phi_eq hd hf
  exact hK h hh

end PositivityTheory.RgUd.TP.Desc.Restr.Ppull2B
end
end

section
noncomputable section

open Matrix Polynomial Set

namespace PositivityTheory.RgUd.TP.Desc.Restr.Ppull2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Restr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isClosed_charpoly_eq {N : ℕ} (c : k[X]) : IsClosed {A : Matrix (Fin N) (Fin N) k | A.charpoly = c} := by
  have hc : ∀ (i : ℕ) (A : Matrix (Fin N) (Fin N) k), A.charpoly.coeff i =
      MvPolynomial.eval (fun p : Fin N × Fin N => A p.1 p.2)
        (MvPolynomial.map (Int.castRingHom k) ((Matrix.charpoly.univ ℤ (Fin N)).coeff i)) := by
    intro i A
    have h := Matrix.charpoly.univ_map_eval₂Hom (Fin N) (Int.castRingHom k) (fun p : Fin N × Fin N => A p.1 p.2)
    have hA : Matrix.of (Function.curry (fun p : Fin N × Fin N => A p.1 p.2)) = A := by
      ext a b
      rfl
    rw [hA] at h
    rw [← h, Polynomial.coeff_map, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq_eval_map]
  have hset : {A : Matrix (Fin N) (Fin N) k | A.charpoly = c} = ⋂ i : ℕ, {A | A.charpoly.coeff i = c.coeff i} := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact ⟨fun h i => by rw [h], fun h => Polynomial.ext h⟩
  rw [hset]
  refine isClosed_iInter fun i => ?_
  simp only [hc]
  exact isClosed_eq ((MvPolynomial.continuous_eval _).comp
    (continuous_pi fun p => continuous_id.matrix_elem p.1 p.2)) continuous_const

theorem conj_mem_Bz {n : ℕ} {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {g : GL (Fin n) k} (hg : g ∈ Gz Z)
    {x : Matrix (Fin n) (Fin n) k} (hx : x ∈ Bz Z) : g.val * x * g⁻¹.val ∈ Bz Z := by
  have hg' : ∀ a ∈ Z, a * g.val = g.val * a := hg
  have hx' : ∀ a ∈ Z, a * x = x * a := hx
  show ∀ a ∈ Z, a * (g.val * x * g⁻¹.val) = g.val * x * g⁻¹.val * a
  intro a ha
  have hi : a * g⁻¹.val = g⁻¹.val * a := by
    have e := congrArg (fun m => g⁻¹.val * m * g⁻¹.val) (hg' a ha)
    simp only [mul_assoc, Units.mul_inv, mul_one, Units.inv_mul_cancel_left] at e
    exact e.symm
  calc a * (g.val * x * g⁻¹.val) = a * g.val * x * g⁻¹.val := by simp only [mul_assoc]
    _ = g.val * (a * x) * g⁻¹.val := by rw [hg' a ha]; simp only [mul_assoc]
    _ = g.val * x * (a * g⁻¹.val) := by rw [hx' a ha]; simp only [mul_assoc]
    _ = g.val * x * g⁻¹.val * a := by rw [hi]; simp only [mul_assoc]

theorem pullPieces : PullPieces k := by
  unfold PullPieces
  intro n N q Z Z' φ e hZ hD χ
  have hBz : ∀ {m : ℕ} (S : Subalgebra k (Matrix (Fin m) (Fin m) k)), IsClosed (Bz S) := by
    intro m S
    have hS : Bz S = ⋂ a ∈ S, {x : Matrix (Fin m) (Fin m) k | a * x = x * a} := by
      ext x
      simp only [Set.mem_iInter]
      rfl
    rw [hS]
    exact isClosed_biInter fun a _ =>
      isClosed_eq (continuous_const.matrix_mul continuous_id) (continuous_id.matrix_mul continuous_const)
  obtain ⟨P, hP0, hP⟩ : ∃ P : k[X], P ≠ 0 ∧
      ∀ x : Matrix (Fin n) (Fin n) k, x.charpoly = χ → aeval (φ x) P = 0 := by
    by_cases hχ : χ = 0
    · exact ⟨1, one_ne_zero, fun x hx => absurd (hx.trans hχ) (Matrix.charpoly_monic x).ne_zero⟩
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      refine ⟨1, one_ne_zero, fun x _ => ?_⟩
      ext i j
      exact i.elim0
    · obtain ⟨hq, -⟩ := Ppull2A.choose_zero hD hN
      refine ⟨expand k q χ, ?_, fun x hx => Ppull2A.aeval_expand hD hN χ x (hx ▸ Matrix.aeval_self_charpoly x)⟩
      rwa [Ne, Polynomial.expand_eq_zero (by omega)]
  obtain ⟨l, hnd, hl⟩ := Ppull2A.finite_charpoly N P hP0
  refine ⟨l, fun h => ?_⟩
  choose M F' hP' hG' using h
  unfold IsPieces at hP'
  let L : Fin l.length → k[X] := fun j => l[j.val]'j.isLt
  have hLm : ∀ j, L j ∈ l := fun j => List.getElem_mem j.isLt
  let mj : Fin l.length → ℕ := fun j => M (L j) (hLm j)
  let G : (Σ j : Fin l.length, Fin (mj j)) → Set (Matrix (Fin n) (Fin n) k) := fun s =>
    {x | x ∈ Bz Z ∧ x.charpoly = χ ∧ (φ x).charpoly = L s.1 ∧ φ x ∈ F' (L s.1) (hLm s.1) s.2}
  have memG : ∀ s x, x ∈ G s ↔ (x ∈ Bz Z ∧ x.charpoly = χ ∧ (φ x).charpoly = L s.1 ∧
      φ x ∈ F' (L s.1) (hLm s.1) s.2) := fun _ _ => Iff.rfl
  have hGc : ∀ s, IsClosed (G s) ∧ G s ⊆ Bz Z ∧
      ∀ g ∈ Gz Z, ∀ x ∈ G s, (g : Matrix (Fin n) (Fin n) k) * x * ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ∈ G s := by
    rintro ⟨j, i⟩
    refine ⟨?_, fun x hx => ((memG _ x).1 hx).1, ?_⟩
    · exact (hBz Z).inter ((isClosed_charpoly_eq χ).inter
        (((isClosed_charpoly_eq _).preimage hD.emb.continuous).inter
          (((hP' _ _).1 i).1.preimage hD.emb.continuous)))
    · intro g hg x hx
      obtain ⟨hxB, hxc, hxφc, hxF⟩ := (memG _ x).1 hx
      let g' : GL (Fin N) k := Units.map (φ : Matrix (Fin n) (Fin n) k →* Matrix (Fin N) (Fin N) k) g
      have hg' : g' ∈ Gz Z' := (hD.gz g').2 ⟨g, hg, rfl⟩
      have hφ : φ (g.val * x * g⁻¹.val) = g'.val * φ x * g'⁻¹.val := by
        rw [map_mul, map_mul]
        rfl
      refine (memG _ _).2 ⟨conj_mem_Bz hg hxB, ?_, ?_, ?_⟩
      · rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj]
        exact hxc
      · show (φ (g.val * x * g⁻¹.val)).charpoly = _
        rw [hφ, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
        exact hxφc
      · show φ (g.val * x * g⁻¹.val) ∈ _
        rw [hφ]
        exact ((hP' _ _).1 i).2.2 g' hg' _ hxF
  have hGd : ∀ s s', s ≠ s' → Disjoint (G s) (G s') := by
    rintro ⟨j, i⟩ ⟨j', i'⟩ hne
    rw [Set.disjoint_left]
    intro x hx1 hx2
    obtain ⟨-, -, hc1, hF1⟩ := (memG _ x).1 hx1
    obtain ⟨-, -, hc2, hF2⟩ := (memG _ x).1 hx2
    by_cases hj : j = j'
    · subst hj
      have hi : i ≠ i' := fun h => hne (by rw [h])
      exact Set.disjoint_left.1 ((hP' _ _).2.1 i i' hi) hF1 hF2
    · apply hj
      have hL : L j = L j' := hc1.symm.trans hc2
      exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 hL)
  have hGcov : ∀ x ∈ Bz Z, x.charpoly = χ → ∃ s, x ∈ G s := by
    intro x hx hc
    obtain ⟨j0, hj0, hj0e⟩ := List.getElem_of_mem (hl (φ x) (hP x hc))
    let j : Fin l.length := ⟨j0, hj0⟩
    have hxB' : φ x ∈ Bz Z' := by
      rw [hD.cen]
      exact ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := (hP' (L j) (hLm j)).2.2 (φ x) hxB' hj0e.symm
    exact ⟨⟨j, i⟩, (memG _ x).2 ⟨hx, hc, hj0e.symm, hi⟩⟩
  have hGg : ∀ s, Good Z (G s) := by
    rintro ⟨j, i⟩
    have hg := hG' (L j) (hLm j) i
    unfold Good at hg ⊢
    rcases hg with ⟨c', hc', hnil⟩ | ⟨N', S, hS, hmu, hV⟩
    · have hcc : c' ∈ φ '' (Z : Set (Matrix (Fin n) (Fin n) k)) := by
        rw [← hD.carrier]
        exact hc'
      obtain ⟨c, hc, rfl⟩ := hcc
      refine Or.inl ⟨c, hc, fun x hx => ?_⟩
      obtain ⟨m, hm⟩ := hnil (φ x) ((memG _ x).1 hx).2.2.2
      exact ⟨m, hD.inj (by rw [map_pow, map_sub, hm, map_zero])⟩
    · refine Or.inr ⟨N', S, hS, by rw [← hD.mu]; exact hmu, fun hv =>
        Ppull2B.fibVan_pull hD _ _ (fun x hx => ((memG _ x).1 hx).2.2.2) (hV hv)⟩
  refine ⟨∑ j, mj j, fun t => G (finSigmaFinEquiv.symm t), ?_, fun t => hGg _⟩
  unfold IsPieces
  refine ⟨fun t => hGc _, fun t t' htt => hGd _ _ (fun h => htt (finSigmaFinEquiv.symm.injective h)), ?_⟩
  intro x hx hc
  obtain ⟨s, hs⟩ := hGcov x hx hc
  exact ⟨finSigmaFinEquiv s, by simpa using hs⟩

end PositivityTheory.RgUd.TP.Desc.Restr.Ppull2
end
end

section
namespace PositivityTheory.RgUd.TP.Desc.Restr.Final

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Restr

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem restrL (hP : PhiEx k) (hQ : PullPieces k) : RestrL k := by
  intro p _ _ n Z hZ
  obtain ⟨c, hc⟩ : ∃ c : ℕ, n ≤ p ^ c := ⟨n, (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le⟩
  obtain ⟨N, Z', φ, e, hd⟩ := hP p c n Z hZ hc
  exact ⟨N, p ^ c, Z', hd.cr, hd.mu, ⟨c, rfl⟩, hd.roots, hd.nil, hQ Z Z' φ e hZ hd⟩

theorem restr : Restr k := restrL k (Pphi1.phiEx k (PfinDim.finDim k)) Ppull2.pullPieces

end PositivityTheory.RgUd.TP.Desc.Restr.Final
end
