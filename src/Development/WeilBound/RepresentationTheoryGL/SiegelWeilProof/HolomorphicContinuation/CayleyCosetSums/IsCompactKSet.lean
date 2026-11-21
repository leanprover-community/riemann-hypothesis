import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DerivativeVacuumDilationsAlt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.NormDetFirstBlockCompact
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.RowsBlocks
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FactorL
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.ContinuousSecondCayleyBlockMapBis
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.MapsToUpToSign

section
noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.GRH

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem continuous_mR : Continuous (mR : GR n → M2 n) :=
  Units.continuous_val.comp continuous_subtype_val

instance m2LC (n : ℕ) : LocallyCompactSpace (M2 n) :=
  inferInstanceAs (LocallyCompactSpace (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℂ))

instance secondCountableBlockMatrices (n : ℕ) : SecondCountableTopology (M2 n) :=
  inferInstanceAs (SecondCountableTopology (Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℂ))

theorem JJ_mul_self : JJ n * JJ n = -1 := by
  rw [JJ, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add, neg_zero]
  rw [← fromBlocks_one, fromBlocks_neg, neg_zero]

theorem isClosed_inG : IsClosed {x : M2 n | InG x} :=
  isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const

theorem inv_left {x : M2 n} (hx : InG x) : (-(JJ n * xᴴ * JJ n)) * x = 1 := by
  unfold InG at hx
  have h : JJ n * xᴴ * JJ n * x = JJ n * (xᴴ * JJ n * x) := by
    simp only [Matrix.mul_assoc]
  rw [Matrix.neg_mul, h, hx, JJ_mul_self, neg_neg]

def toSet : GR n ≃ₜ {x : M2 n | InG x} where
  toFun g := ⟨mR g, g.2⟩
  invFun x := ⟨⟨x.1, -(JJ n * x.1ᴴ * JJ n), mul_eq_one_comm.mp (inv_left x.2), inv_left x.2⟩, x.2⟩
  left_inv g := by
    apply Subtype.ext
    apply Units.ext
    rfl
  right_inv x := rfl
  continuous_toFun := continuous_mR.subtype_mk _
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    exact ((continuous_const.matrix_mul (continuous_subtype_val.matrix_conjTranspose)).matrix_mul continuous_const).neg

theorem isClosedEmbedding_mR : Topology.IsClosedEmbedding (mR : GR n → M2 n) :=
  (isClosed_inG.isClosedEmbedding_subtypeVal).comp toSet.isClosedEmbedding

theorem isCompact_preimage_mR {C : Set (M2 n)} (hC : IsCompact C) : IsCompact ((mR : GR n → M2 n) ⁻¹' C) :=
  isClosedEmbedding_mR.isCompact_preimage hC

instance : LocallyCompactSpace (GR n) := isClosedEmbedding_mR.locallyCompactSpace

instance : MeasurableSpace (GR n) := borel _

instance : BorelSpace (GR n) := ⟨rfl⟩

instance : SecondCountableTopology (GR n) := isClosedEmbedding_mR.isEmbedding.secondCountableTopology

end PositivityTheory.Rg.Sw.HSt.GRH
end
end

section
noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt.GRH

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

instance krCpt (n : ℕ) : CompactSpace (KR n) := kRCpt n

def phi (m : ℕ) (e : ℤ) (w : ℂ) (u : GR n) : ℂ := F0 m 0 e u * ((hLoc u : ℝ) : ℂ) ^ w

def tw (m : ℕ) (e : ℤ) (μK : Measure (KR n)) (β : M2 n → ℝ) (X : M2 n) : ℂ :=
  ∫ k : KR n, (F0 m 0 e (k : GR n))⁻¹ * (β ((mR (k : GR n))ᴴ * X) : ℂ) ∂μK

def cw (m : ℕ) (e : ℤ) (ν : Measure (GR n)) (μK : Measure (KR n)) (β : M2 n → ℝ) (w : ℂ) : ℂ :=
  ∫ u : GR n, phi m e w u * tw m e μK β (mR u) ∂ν

theorem mR_mul (g h : GR n) : mR (g * h) = mR g * mR h := rfl

theorem tw_left (m : ℕ) (e : ℤ) (μK : Measure (KR n)) [μK.IsMulLeftInvariant] (β : M2 n → ℝ) (k₀ : KR n) (X : M2 n) :
    tw m e μK β (mR (k₀ : GR n) * X) = (F0 m 0 e (k₀ : GR n))⁻¹ * tw m e μK β X := by
  have h := integral_mul_left_eq_self (μ := μK)
    (fun k : KR n => (F0 m 0 e (k : GR n))⁻¹ * (β ((mR (k : GR n))ᴴ * (mR (k₀ : GR n) * X)) : ℂ)) k₀
  rw [tw, ← h, tw, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  have hk0 : (mR (k₀ : GR n))ᴴ * mR (k₀ : GR n) = 1 := k₀.2.2
  have hmul := ((mult n m 0 e).1 (k₀ : GR n) (k : GR n) k.2).1
  simp only [Subgroup.coe_mul, mR_mul]
  rw [hmul, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (mR (k₀ : GR n))ᴴ, hk0, Matrix.one_mul,
    mul_inv]
  ring

theorem conv_phi (m : ℕ) (e : ℤ) (ν : Measure (GR n)) [ν.IsMulLeftInvariant] (μK : Measure (KR n)) [μK.IsMulLeftInvariant]
    (β : M2 n → ℝ) (w : ℂ) (y : GR n) :
    ∫ u : GR n, phi m e w (y * u) * tw m e μK β (mR u) ∂ν = cw m e ν μK β w * phi m e w y := by
  obtain ⟨p, k, hp, hk, rfl⟩ := iwa n y
  have hnn : ∀ g : GR n, 0 ≤ hLoc g := fun g => by unfold hLoc; positivity
  have hphi : ∀ g : GR n, phi m e w (p * g) = phi m e w p * phi m e w g := by
    intro g
    obtain ⟨h1, h2⟩ := (mult n m 0 e).2 p g hp
    simp only [phi, h1, h2, Complex.ofReal_mul]
    rw [Complex.mul_cpow_ofReal_nonneg (hnn p) (hnn g)]
    ring
  have hK : phi m e w (p * k) = phi m e w p * F0 m 0 e k := by
    obtain ⟨h1, h2⟩ := (mult n m 0 e).1 p k hk
    simp only [phi, h1, h2]
    ring
  have hone : F0 m 0 e (1 : GR n) = 1 := by
    have h1 : toBlocks₂₁ (1 : M2 n) = 0 := by
      ext i j; simp [Matrix.toBlocks₂₁, Matrix.one_apply]
    have h2 : toBlocks₂₂ (1 : M2 n) = 1 := by
      ext i j; simp [Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.one_apply]
    simp [F0, mR, f0, u1, u2, h1, h2]
  have hF : F0 m 0 e k * F0 m 0 e k⁻¹ = 1 := by
    rw [← ((mult n m 0 e).1 k k⁻¹ (inv_mem hk)).1, mul_inv_cancel, hone]
  have htw : ∀ u : GR n, tw m e μK β (mR (k⁻¹ * u)) = F0 m 0 e k * tw m e μK β (mR u) := by
    intro u
    rw [mR_mul]
    have h := tw_left m e μK β (⟨k⁻¹, inv_mem hk⟩ : KR n) (mR u)
    simp only at h
    rw [h, inv_eq_of_mul_eq_one_left hF]
  calc ∫ u : GR n, phi m e w (p * k * u) * tw m e μK β (mR u) ∂ν
      = ∫ u : GR n, phi m e w (p * k * (k⁻¹ * u)) * tw m e μK β (mR (k⁻¹ * u)) ∂ν :=
        (integral_mul_left_eq_self (fun u => phi m e w (p * k * u) * tw m e μK β (mR u)) k⁻¹).symm
    _ = ∫ u : GR n, (F0 m 0 e k * phi m e w p) * (phi m e w u * tw m e μK β (mR u)) ∂ν := by
        congr 1
        funext u
        rw [show p * k * (k⁻¹ * u) = p * u by group, hphi, htw]
        ring
    _ = cw m e ν μK β w * phi m e w (p * k) := by
        rw [integral_const_mul, hK]
        unfold cw
        ring

end PositivityTheory.Rg.Sw.HSt.Conv
end
end

section
noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt.GRH

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem continuous_kR : Continuous (fun k : KR n => mR (k : GR n)) := continuous_mR.comp continuous_subtype_val

def kSet (S : Set (M2 n)) : Set (M2 n) := (fun p : KR n × M2 n => mR (p.1 : GR n) * p.2) '' (univ ×ˢ S)

theorem isCompact_kSet {S : Set (M2 n)} (hS : IsCompact S) : IsCompact (kSet S) :=
  (isCompact_univ.prod hS).image ((continuous_kR.comp continuous_fst).mul continuous_snd)

theorem tw_eq_zero (m : ℕ) (e : ℤ) (μK : Measure (KR n)) (β : M2 n → ℝ) {X : M2 n} (hX : X ∉ kSet (tsupport β)) :
    tw m e μK β X = 0 := by
  unfold tw
  have hz : ∀ k : KR n, β ((mR (k : GR n))ᴴ * X) = 0 := by
    intro k
    by_contra h
    apply hX
    have hk : InK (mR (k : GR n)) := k.2
    have hkk : mR (k : GR n) * (mR (k : GR n))ᴴ = 1 := mul_eq_one_comm.mp hk.2
    refine ⟨(k, (mR (k : GR n))ᴴ * X), ⟨mem_univ _, subset_tsupport _ h⟩, ?_⟩
    simp only
    rw [← Matrix.mul_assoc, hkk, Matrix.one_mul]
  simp [hz]

theorem tw_support (m : ℕ) (e : ℤ) (μK : Measure (KR n)) {β : M2 n → ℝ} (hβ : HasCompactSupport β) :
    HasCompactSupport (tw m e μK β) := by
  refine HasCompactSupport.intro (isCompact_kSet hβ) fun X hX => tw_eq_zero m e μK β hX

private theorem JJ_mul_JJ' : JJ n * JJ n = -1 := by
  rw [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  simp

private theorem mul_JJ_mul_conjTranspose_of_inG {x : M2 n} (hx : InG x) : x * JJ n * xᴴ = JJ n := by
  have hJ := (JJ_mul_JJ' (n := n))
  have hx' : xᴴ * JJ n * x = JJ n := hx
  have h1 : (-(JJ n * xᴴ * JJ n)) * x = 1 := by
    calc (-(JJ n * xᴴ * JJ n)) * x = -(JJ n * (xᴴ * JJ n * x)) := by
          simp only [Matrix.neg_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hx', hJ, neg_neg]
  have h2 : x * (-(JJ n * xᴴ * JJ n)) = 1 := mul_eq_one_comm.mp h1
  calc x * JJ n * xᴴ = x * (-(JJ n * xᴴ * JJ n)) * JJ n := by
        simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, hJ, Matrix.mul_one, neg_neg]
    _ = JJ n := by rw [h2, Matrix.one_mul]

private theorem toBlocks₂_conj_relations_of_inG {x : M2 n} (hx : InG x) :
    toBlocks₂₁ x * (toBlocks₂₂ x)ᴴ = toBlocks₂₂ x * (toBlocks₂₁ x)ᴴ ∧
    toBlocks₂₁ x * (toBlocks₁₂ x)ᴴ - toBlocks₂₂ x * (toBlocks₁₁ x)ᴴ = -1 := by
  have e := mul_JJ_mul_conjTranspose_of_inG hx
  rw [← fromBlocks_toBlocks x] at e
  simp only [JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_inj,
    toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂] at e
  simp at e
  refine ⟨?_, ?_⟩
  · have h := e.2.2.2
    rw [neg_add_eq_sub, sub_eq_zero] at h
    exact h
  · have h := e.2.2.1
    rwa [neg_add_eq_sub] at h

private theorem det_smul_toBlocks₂₁_add_toBlocks₂₂_ne_zero_of_inG {x : M2 n} (hx : InG x) (t : ℂ) (ht : t ≠ star t) :
    (t • toBlocks₂₁ x + toBlocks₂₂ x).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hvM⟩ := exists_vecMul_eq_zero_iff.mpr h0
  obtain ⟨hC, hA⟩ := toBlocks₂_conj_relations_of_inG hx
  rw [Matrix.vecMul_add, Matrix.vecMul_smul] at hvM
  have hβ : v ᵥ* toBlocks₂₂ x = -t • (v ᵥ* toBlocks₂₁ x) := by
    rw [neg_smul, ← sub_eq_zero, sub_neg_eq_add, add_comm]
    exact hvM
  have key : (v ᵥ* toBlocks₂₁ x) ⬝ᵥ star (v ᵥ* toBlocks₂₂ x)
      = (v ᵥ* toBlocks₂₂ x) ⬝ᵥ star (v ᵥ* toBlocks₂₁ x) := by
    have h := congrArg (fun M => (v ᵥ* M) ⬝ᵥ star v) hC
    have e1 : (v ᵥ* (toBlocks₂₁ x * (toBlocks₂₂ x)ᴴ)) ⬝ᵥ star v
        = (v ᵥ* toBlocks₂₁ x) ⬝ᵥ star (v ᵥ* toBlocks₂₂ x) := by
      rw [← vecMul_vecMul, ← dotProduct_mulVec, star_vecMul]
    have e2 : (v ᵥ* (toBlocks₂₂ x * (toBlocks₂₁ x)ᴴ)) ⬝ᵥ star v
        = (v ᵥ* toBlocks₂₂ x) ⬝ᵥ star (v ᵥ* toBlocks₂₁ x) := by
      rw [← vecMul_vecMul, ← dotProduct_mulVec, star_vecMul]
    rw [← e1, ← e2]
    exact h
  rw [hβ, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at key
  have hs : (v ᵥ* toBlocks₂₁ x) ⬝ᵥ star (v ᵥ* toBlocks₂₁ x) = 0 := by
    have h3 : (t - star t) * ((v ᵥ* toBlocks₂₁ x) ⬝ᵥ star (v ᵥ* toBlocks₂₁ x)) = 0 := by
      rw [star_neg] at key
      linear_combination key
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd (sub_eq_zero.mp h4) ht
    · exact h4
  have hα : v ᵥ* toBlocks₂₁ x = 0 := by
    open scoped ComplexOrder in exact dotProduct_self_star_eq_zero.mp hs
  have hβ0 : v ᵥ* toBlocks₂₂ x = 0 := by rw [hβ, hα, smul_zero]
  have h5 := congrArg (fun M => v ᵥ* M) hA
  simp only [Matrix.vecMul_sub, ← vecMul_vecMul, hα, hβ0, zero_vecMul, sub_self, vecMul_neg,
    vecMul_one] at h5
  exact hv (neg_eq_zero.mp h5.symm)

end PositivityTheory.Rg.Sw.HSt.Conv
end
end
