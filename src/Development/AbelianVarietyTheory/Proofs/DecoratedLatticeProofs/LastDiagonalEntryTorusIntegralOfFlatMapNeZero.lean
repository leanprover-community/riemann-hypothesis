module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOff
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulMemLatO
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRangeOfOneTmulMem
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OneEqSumPlaceIdempotentsOverTwoAddTwoMul

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.LastDiag

variable {D : D7}

theorem smul_mem_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * y i) ∈ latA S L P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, x, hx, ?_⟩
    funext i
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (0 : Fin S.rank → AE D) i) = 0 := by
      funext i; simp
    rw [this]; exact zero_mem _
  | add z z' _ _ hz hz' =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (z + z') i) =
        (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z i) + (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z' i) := by
      funext i; simp [mul_add]
    rw [this]; exact add_mem hz hz'
  | neg z _ hz =>
    have : (fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (-z) i) =
        -(fun i => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * z i) := by
      funext i; simp
    rw [this]; exact neg_mem hz

end GlobalTheory.FinPl.LastDiag

namespace GlobalTheory.FinPl.LastDiag

variable {D : D7}

theorem mxAt_mul_left {P : Pl D → Prop} {a b c : ℕ} (y : Mx D a b) {x : Mx D b c} (hx : MxAt P x) :
    MxAt P (y ⬝ x) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hx l j)

theorem mxAt_mul_right {P : Pl D → Prop} {a b c : ℕ} {x : Mx D a b} (hx : MxAt P x) (y : Mx D b c) :
    MxAt P (x ⬝ y) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx i l)

theorem jX_pX_mem_latV {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) {L : Lat T} {L₀ : Lat T₀} {v : Pl D}
    (hm : MonoAt d L L₀ v) {u : Fin T.rank → AE D} (hu : u ∈ latV T L (· = v)) :
    d.jX *ᵥ (d.pX *ᵥ u) ∈ latV T L (· = v) := by
  have h := ((hm u).1 hu).1
  have heq : d.jX *ᵥ (d.pX *ᵥ u) = ∑ i, colMul d.jX i ((d.pX *ᵥ u) i) := by
    funext k
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, colMul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [heq]
  exact sum_mem fun i _ => h i

theorem jX_pX_mem_latA {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) {L : Lat T} {L₀ : Lat T₀} {v : Pl D}
    (hm : MonoAt d L L₀ v) {z : Fin T.rank → AE D} (hz : z ∈ latA T L (· = v)) :
    d.jX *ᵥ (d.pX *ᵥ z) ∈ latA T L (· = v) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    set u : Fin T.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hu
    have hu' : u ∈ latV T L (· = v) := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have heq : d.jX *ᵥ (d.pX *ᵥ (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i))) =
        fun k => ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (d.jX *ᵥ (d.pX *ᵥ u)) k := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      funext k
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, hu]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i) =
          ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) * (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul]
      rw [h1]; ring
    rw [heq]
    exact smul_mem_latA ha (jX_pX_mem_latV d hm hu')
  | zero => rw [Matrix.mulVec_zero, Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add, Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg, Matrix.mulVec_neg]; exact neg_mem hz

theorem wittExtZero_inclusionX_mem_homLatticeCompletion {S S₀ T T₀ : HSp D} {ρ σ : ℕ} (dS : HypDec S S₀ ρ) (dT : HypDec T T₀ σ) {LS : Lat S}
    {LS₀ : Lat S₀} {LT : Lat T} {LT₀ : Lat T₀} {v : Pl D} (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT)
    (hS₀ : IsSelfDualC S₀ LS₀) (hmS : MonoAt dS LS LS₀ v) (hmT : MonoAt dT LT LT₀ v) {w : WO S₀ T}
    (hw : w ∈ latO S₀ T (LS₀ : Set _) (LT : Set _) (· = v)) :
    dS.ext0 T (dT.incX S₀ (dT.pX ⬝ w)) ∈ latO S T (LS : Set _) (LT : Set _) (· = v) := by
  have hx := GlobalTheory.FinPl.LatMem.latO_mxAt hw
  refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT (· = v) _).2 ⟨?_, fun y hy => ?_⟩
  · rw [HypDec.matrixExtendByZero_apply, HypDec.incX_apply]
    exact mxAt_mul_right (mxAt_mul_left _ (mxAt_mul_left _ hx)) _
  · change (dT.jX * (dT.pX * w) * dS.p0) *ᵥ y ∈ latA T LT (· = v)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h1 : dS.p0 *ᵥ y ∈ latV S₀ LS₀ (· = v) := ((hmS y).1 hy).2.2
    exact jX_pX_mem_latA dT hmT (GlobalTheory.FinPl.LatMem.latO_maps hS₀ hw h1)

end GlobalTheory.FinPl.LastDiag

namespace GlobalTheory.FinPl.LastDiag

variable {D : D7}

theorem incAdj_smul {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (c : AE D) (y : Mx D S.rank ρ) :
    d.incAdj S (c • y) = cA D c • d.incAdj S y := by
  rw [HypDec.incAdj_apply, HypDec.incAdj_apply, HypDec.incY_apply, HypDec.incY_apply, adj_smul, Matrix.smul_mul,
    smul_comm (incA D (-D.host.xi0⁻¹)) (cA D c), Matrix.mul_smul]

theorem symplO_incAdj_proj {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (z : Mx D S.rank ρ) (w : WO S T) :
    symplO S T (d.incAdj S z) w = symplO S T (d.incAdj S z) (d.incX S (d.pX ⬝ w)) := by
  have key : hO S T (d.incAdj S z) w = hO S T (d.incAdj S z) (d.incX S (d.pX ⬝ w)) := by
    rw [d.hO_coordT S, d.hO_coordT S]
    simp only [HypDec.incAdj_apply, HypDec.incY_apply, HypDec.incX_apply, ← Matrix.mul_assoc, HypDec.pX_jY,
      HypDec.p0_jY, HypDec.pY_jY, HypDec.pX_jX, HypDec.p0_jX, HypDec.pY_jX, Matrix.zero_mul, Matrix.one_mul]
    simp [pairT, hO]
  rw [symplO, symplO, key]

end GlobalTheory.FinPl.LastDiag

namespace GlobalTheory.FinPl.LastDiag

variable {D : D7}

theorem symplO_add_right' (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  simp only [symplO, hO, Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem half_smul_mem {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {v : Pl D} (h2 : (2 : 𝓞 D.host.F) ∉ v.asIdeal) {u : WO S T} (hu : u ∈ latO S T LS LT (· = v)) :
    (pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v) * algebraMap D.host.F (Af D.host.F) (2 : D.host.F)⁻¹)
      ⊗ₜ[D.host.F] (1 : D.host.E)) • u ∈ latO S T LS LT (· = v) := by
  classical
  set γ := GlobalTheory.FinPl.LatMem.indP D.host.F (· = v) * algebraMap D.host.F (Af D.host.F) (2 : D.host.F)⁻¹ with hγ
  have hγi : γ ∈ intAf D.host.F := fun w => by
    rw [hγ, map_mul, AlgHom.commutes, GlobalTheory.FinPl.LatMem.evalV_indP]
    split_ifs with hw
    · subst hw; rw [one_mul]; exact GlobalTheory.LatVac.half_mem_adicCompletionIntegers _ _ h2
    · rw [zero_mul]; exact zero_mem _
  induction hu using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, s, hs, t, ht, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨γ * β, GlobalTheory.FinPl.LatMem.intAf_mul' hγi hβi,
      fun w hw => by rw [map_mul, hβ w hw, mul_zero], a, ha, s, hs, t, ht, ?_⟩
    ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [show pairA D.host.F 0 γ * pairA D.host.F 0 β = pairA D.host.F 0 (γ * β) from Prod.ext (mul_zero _) rfl]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

end GlobalTheory.FinPl.LastDiag

namespace GlobalTheory.FinPl.LastDiag

variable {D : D7}

theorem exists_idemAt (D : D7) (v : Pl D) : ∃ e : AE D, e ∈ intAt D (· = v) ∧ (∀ a ∈ idAt D (· = v), a * e = a) ∧
    cA D e = e ∧ ((2 : 𝓞 D.host.F) ∉ v.asIdeal → ∃ c : AE D, c + c = e ∧ ∀ (S T : HSp D)
      (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (u : WO S T),
        u ∈ latO S T LS LT (· = v) → c • u ∈ latO S T LS LT (· = v)) := by
  have hid : pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] (1 : D.host.E) ∈ idAt D (· = v) :=
    GlobalTheory.FinPl.LatMem.tmul_mem_idAt (GlobalTheory.FinPl.LatMem.indicatorAdele_supported _ _) 1
  have hact : ∀ a ∈ idAt D (· = v),
      a * (pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] (1 : D.host.E)) = a :=
    fun a ha => GlobalTheory.FinPl.LatMem.mul_indP ha
  refine ⟨_, ⟨hid, GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hact _ hid])⟩, hact,
    GlobalTheory.SelfDualAt.cA_alg _, fun h2 => ⟨_, ?_, fun S T LS LT u hu => half_smul_mem h2 hu⟩⟩
  rw [← TensorProduct.add_tmul]
  congr 1
  refine Prod.ext (add_zero _) ?_
  show _ * _ + _ * _ = _
  rw [← mul_add, ← map_add (f := _), show (2 : D.host.F)⁻¹ + 2⁻¹ = 1 by norm_num, map_one, mul_one]
  all_goals rfl

theorem yZero_mul_diag (S : HSp D) {ρ : ℕ} (z : Fin S.rank → D.host.E) (t : Matrix (Fin ρ) (Fin ρ) (AE D))
    (ht : ∀ i j, i ≠ j → t i j = 0) (i : Fin ρ) (hi : i.1 + 1 = ρ) : yZero S ρ z ⬝ t = t i i • yZero S ρ z := by
  classical
  have hell : ∀ j : Fin ρ, ell D ρ j = if j = i then 1 else 0 := fun j => by
    by_cases hj : j = i
    · subst hj; simp [ell, hi]
    · have hj' : ¬ (j.1 + 1 = ρ) := fun h => hj (Fin.ext (by omega))
      simp [ell, hj', hj]
  ext k l
  have hy : ∀ j, yZero S ρ z k j = if j = i then -ratV z k else 0 := fun j => by
    simp only [yZero, zEll, Matrix.neg_apply, Matrix.vecMulVec_apply, hell]
    split_ifs <;> simp
  rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, hy l]
  simp only [hy, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hl : l = i
  · subst hl; rw [if_pos rfl, mul_comm]
  · rw [if_neg hl, ht i l (Ne.symm hl), mul_zero, mul_zero]

theorem symplO_incAdj_eq {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (z : Mx D S.rank ρ) (w : WO S T) :
    symplO S T (d.incAdj S z) w = -Algebra.trace (AF D.host.F) (AE D) (z ⬝ (d.pX ⬝ w)).trace := by
  rw [symplO_incAdj_proj, GlobalTheory.SplitScalar.symplO_skew, HypDec.symplO_incX_incAdj]

end GlobalTheory.FinPl.LastDiag

namespace GlobalTheory.FinPl.LastDiag

variable {D : D7}

theorem mxAt_smul {P : Pl D → Prop} {m n : ℕ} (c : AE D) {x : Mx D m n} (hx : MxAt P x) : MxAt P (c • x) :=
  fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_left _ _ (hx i j)

theorem smul_isHalf' {e : AE D} (he : e * e = e) {m n : ℕ} (u : Mx D m n) : IsHalf e (e • u) := by
  intro i j
  rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he]

theorem smul_eq_self {P : Pl D → Prop} {e : AE D} (he : ∀ a ∈ idAt D P, e * a = a) {m n : ℕ} {x : Mx D m n}
    (hx : MxAt P x) : e • x = x := by
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul]
  exact he _ (hx i j)

theorem add_smul_mx {m n : ℕ} (a b : AE D) (x : Mx D m n) : a • x + b • x = (a + b) • x := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul]

end GlobalTheory.FinPl.LastDiag

namespace GlobalTheory.FinPl.LastDiag

end GlobalTheory.FinPl.LastDiag
