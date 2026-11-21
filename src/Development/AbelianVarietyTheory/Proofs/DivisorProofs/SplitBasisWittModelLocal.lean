import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearWittModelLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticSelfZeroSplitSupported
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqSumSplitPlacePartsStatement

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LatInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}

theorem piW_smul_incl (v : Pl F) (t : E →ₐ[F] Fv F v) (a : AF F) (e : E) :
    piW t (a • inclR (F := F) (AF F) e) = evFin F v a * t e := by
  simp [piW, inclR, compFin, TensorProduct.smul_tmul', splitProj_tmul]

theorem comp_mem_splitLat (v : Pl F) (t : E →ₐ[F] Fv F v) {L : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E}
    (hx : x ∈ L) : (fun i => t (x i)) ∈ splitLat t L := by
  refine ⟨_, tmul_mem_latLoc (one_mem _) hx, funext fun i => ?_⟩
  simp [splitVec, splitProj_tmul]

end GlobalTheory.LatInt

namespace GlobalTheory.LatInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}

theorem map_piW_gen (v : Pl F) (t : E →ₐ[F] Fv F v) (a : AF F) (x : Fin n → E) (y : Fin d → E) :
    (a • incM F (Matrix.vecMulVec x y)).map (piW t) =
      evFin F v a • Matrix.vecMulVec (fun i => t (x i)) (fun j => t (y j)) := by
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply, Matrix.smul_apply, incM, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [piW_smul_incl, map_mul]

theorem latAtV_comp_integral {n d : ℕ}
    (X : Spc F E n) (W : Spc F E d) (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v))
    (c : GL (Fin d) (Fv F v)) (hb : IsSplitBasis t X.L b) (hc : IsSplitBasis t W.L c) :
    ∀ γ ∈ latAtV X W v, ∀ i j,
      ((b⁻¹).1 * γ.map (piW t) * (c⁻¹).1ᵀ) i j ∈ v.adicCompletionIntegers F := by
  intro γ hγ
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, ha, x, hx, y, hy, rfl⟩ := hz
    have hx' := (hb.mem_iff).1 (comp_mem_splitLat v t hx)
    have hy' := (hc.mem_iff).1 (comp_mem_splitLat v t hy)
    intro i j
    rw [map_piW_gen, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
      Matrix.vecMul_transpose, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    exact mul_mem ha (mul_mem (hx' i) (hy' j))
  | zero => intro i j; simp
  | add γ δ _ _ hγ hδ =>
    intro i j
    rw [Matrix.map_add (piW t) (map_add _), Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
    exact add_mem (hγ i j) (hδ i j)
  | neg γ _ hγ =>
    intro i j
    rw [Matrix.map_neg (piW t) (map_neg _), Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]
    exact neg_mem (hγ i j)

end GlobalTheory.LatInt
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_tensorLattice_component_integral : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : Spc F E n) (W : Spc F E d) (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)),
    IsSplitBasis t X.L b → IsSplitBasis t W.L c → ∀ γ ∈ latAtV X W v, ∀ i j,
      ((b⁻¹).1 * γ.map (piW t) * (c⁻¹).1ᵀ) i j ∈ v.adicCompletionIntegers F := by
  atlas_forward_decl GlobalTheory.LatInt.latAtV_comp_integral
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LatFill
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piW_smul {v : Pl F} (τ : E →ₐ[F] Fv F v) (a : AF F) (z : AE F E) :
    piW τ (a • z) = evFin F v a * piW τ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, mul_add]
  | tmul b x =>
    rw [TensorProduct.smul_tmul']
    change splitProj τ (compFin F E v ((a • b) ⊗ₜ[F] x)) = evFin F v a * splitProj τ (compFin F E v (b ⊗ₜ[F] x))
    simp [compFin, mul_assoc]

theorem piW_inclR {v : Pl F} (τ : E →ₐ[F] Fv F v) (x : E) : piW τ (inclR (F := F) (AF F) x) = τ x := by
  change splitProj τ (compFin F E v ((1 : AF F) ⊗ₜ[F] x)) = τ x
  simp [compFin]

variable {n d : ℕ}

def fillSet (σ : E →ₐ[F] E) (X : Spc F E n) (W : Spc F E d) (v : Pl F) (t : E →ₐ[F] Fv F v) :
    AddSubgroup (Matrix (Fin n) (Fin d) (Fv F v)) where
  carrier := {M | ∃ γ ∈ latAtV X W v, (∀ i j, piW (t.comp σ) (γ i j) = 0) ∧ ∀ i j, piW t (γ i j) = M i j}
  zero_mem' := ⟨0, zero_mem _, fun _ _ => by simp, fun _ _ => by simp⟩
  add_mem' := by
    rintro _ _ ⟨γ, hγ, h1, h2⟩ ⟨γ', hγ', h1', h2'⟩
    exact ⟨γ + γ', add_mem hγ hγ', fun i j => by simp [h1, h1'], fun i j => by simp [h2, h2']⟩
  neg_mem' := by
    rintro _ ⟨γ, hγ, h1, h2⟩
    exact ⟨-γ, neg_mem hγ, fun i j => by simp [h1], fun i j => by simp [h2]⟩

variable {σ : E →ₐ[F] E} {X : Spc F E n} {W : Spc F E d} {v : Pl F} {t : E →ₐ[F] Fv F v}

theorem smul_mem_fillSet {a : Fv F v} (ha : a ∈ v.adicCompletionIntegers F) {M : Matrix (Fin n) (Fin d) (Fv F v)}
    (hM : M ∈ fillSet σ X W v t) : a • M ∈ fillSet σ X W v t := by
  obtain ⟨γ, hγ, h1, h2⟩ := hM
  refine ⟨GlobalTheory.LatVac.liftV v a • γ, (GlobalTheory.LatVac.latAtV_at_stable X W v).2 a ha γ hγ, fun i j => ?_, fun i j => ?_⟩
  · rw [Matrix.smul_apply, piW_smul, h1, mul_zero]
  · rw [Matrix.smul_apply, piW_smul, h2, GlobalTheory.LatVac.evFin_liftV, Matrix.smul_apply, smul_eq_mul]

theorem gen_mem_fillSet (h : IsCMExt F E σ) {x : Fin n → E} (hx : x ∈ X.L) {x' : Fin d → E} (hx' : x' ∈ W.L) :
    Matrix.vecMulVec (fun i => t (x i)) (fun j => t (x' j)) ∈ fillSet σ X W v t := by
  have key : ∀ e ∈ intLoc F E v, ∃ γ ∈ latAtV X W v,
      (∀ i j, piW (t.comp σ) (γ i j) = splitProj (t.comp σ) e * ((t.comp σ) (x i) * (t.comp σ) (x' j))) ∧
      ∀ i j, piW t (γ i j) = splitProj t e * (t (x i) * t (x' j)) := by
    intro e he
    refine intLoc_induction (p := fun e => ∃ γ ∈ latAtV X W v,
      (∀ i j, piW (t.comp σ) (γ i j) = splitProj (t.comp σ) e * ((t.comp σ) (x i) * (t.comp σ) (x' j))) ∧
      ∀ i j, piW t (γ i j) = splitProj t e * (t (x i) * t (x' j))) (fun a ha o => ?_) ⟨0, zero_mem _, fun _ _ => by simp, fun _ _ => by simp⟩ ?_ ?_ he
    · have ho : algebraMap (𝓞 E) E o = (o : E) := rfl
      refine ⟨GlobalTheory.LatVac.liftV v a • incM F (Matrix.vecMulVec (o • x) x'),
        AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.at_liftV v a, by rw [GlobalTheory.LatVac.evFin_liftV]; exact ha,
          _, X.L.smul_mem o hx, x', hx', rfl⟩, fun i j => ?_, fun i j => ?_⟩
      · simp only [Matrix.smul_apply, incM, Matrix.map_apply, piW_smul, piW_inclR, GlobalTheory.LatVac.evFin_liftV,
          Matrix.vecMulVec_apply, Pi.smul_apply, splitProj_tmul, map_mul]
        rw [Algebra.smul_def, map_mul, ho]
        simp only [AlgHom.comp_apply]
        ring
      · simp only [Matrix.smul_apply, incM, Matrix.map_apply, piW_smul, piW_inclR, GlobalTheory.LatVac.evFin_liftV,
          Matrix.vecMulVec_apply, Pi.smul_apply, splitProj_tmul, map_mul]
        rw [Algebra.smul_def, map_mul, ho]
        ring
    · rintro y z ⟨γ, hγ, h1, h2⟩ ⟨γ', hγ', h1', h2'⟩
      exact ⟨γ + γ', add_mem hγ hγ', fun i j => by simp [h1, h1', add_mul],
        fun i j => by simp [h2, h2', add_mul]⟩
    · rintro y ⟨γ, hγ, h1, h2⟩
      exact ⟨-γ, neg_mem hγ, fun i j => by simp [h1], fun i j => by simp [h2]⟩
  obtain ⟨γ, hγ, h1, h2⟩ := key _ (splitIdem_mem h t)
  exact ⟨γ, hγ, fun i j => by simp [h1], fun i j => by simp [h2, Matrix.vecMulVec_apply]⟩

theorem vecMulVec_mem_fillSet (h : IsCMExt F E σ) {y : Fin n → Fv F v ⊗[F] E} (hy : y ∈ latLoc F X.L v)
    {y' : Fin d → Fv F v ⊗[F] E} (hy' : y' ∈ latLoc F W.L v) :
    Matrix.vecMulVec (splitVec t y) (splitVec t y') ∈ fillSet σ X W v t := by
  refine latLoc_induction (p := fun y => Matrix.vecMulVec (splitVec t y) (splitVec t y') ∈ fillSet σ X W v t)
    (fun a ha x hx => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_) hy
  · refine latLoc_induction (p := fun y' => Matrix.vecMulVec (splitVec t fun i => a ⊗ₜ[F] x i) (splitVec t y') ∈
      fillSet σ X W v t) (fun a' ha' x' hx' => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_) hy'
    · have e : Matrix.vecMulVec (splitVec t fun i => a ⊗ₜ[F] x i) (splitVec t fun j => a' ⊗ₜ[F] x' j) =
          (a * a') • Matrix.vecMulVec (fun i => t (x i)) (fun j => t (x' j)) := by
        ext i j; simp [splitVec, Matrix.vecMulVec_apply]; ring
      rw [e]
      exact smul_mem_fillSet (mul_mem ha ha') (gen_mem_fillSet h hx hx')
    · convert zero_mem (fillSet σ X W v t) using 1
      ext i j; simp [splitVec, Matrix.vecMulVec_apply]
    · convert add_mem hy hz using 1
      ext i j; simp [splitVec, Matrix.vecMulVec_apply, mul_add]
    · convert neg_mem hy using 1
      ext i j; simp [splitVec, Matrix.vecMulVec_apply]
  · convert zero_mem (fillSet σ X W v t) using 1
    ext i j; simp [splitVec, Matrix.vecMulVec_apply]
  · convert add_mem hy hz using 1
    ext i j; simp [splitVec, Matrix.vecMulVec_apply, add_mul]
  · convert neg_mem hy using 1
    ext i j; simp [splitVec, Matrix.vecMulVec_apply]

theorem mul_mul_transpose_eq_sum {K : Type} [Field K] (b : Matrix (Fin n) (Fin n) K) (c : Matrix (Fin d) (Fin d) K)
    (A : Matrix (Fin n) (Fin d) K) :
    b * A * cᵀ = ∑ i, ∑ j, A i j • Matrix.vecMulVec (b *ᵥ Pi.single i 1) (c *ᵥ Pi.single j 1) := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.mulVec_single_one,
    Matrix.transpose_apply, Matrix.col_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.LatFill

theorem GlobalTheory.LatFill.exists_latAtV_coord : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ},
    IsCMExt F E σ → ∀ (X : Spc F E n) (W : Spc F E d) (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v))
    (c : GL (Fin d) (Fv F v)), IsSplitBasis t X.L b → IsSplitBasis t W.L c →
    ∀ A : Matrix (Fin n) (Fin d) (Fv F v), (∀ i j, A i j ∈ v.adicCompletionIntegers F) →
      ∃ γ ∈ latAtV X W v, γ.map (piW (t.comp σ)) = 0 ∧ (b⁻¹).1 * γ.map (piW t) * (c⁻¹).1ᵀ = A := by
  intro F E _ _ _ _ _ σ n d h X W v t b c hb hc A hA
  have single_mem : ∀ {m : ℕ} (i : Fin m) (k : Fin m),
      (Pi.single i (1 : Fv F v) : Fin m → Fv F v) k ∈ v.adicCompletionIntegers F := fun i k => by
    by_cases e : k = i
    · subst e; simp
    · simp [e]
  have hT : b.1 * A * c.1ᵀ ∈ GlobalTheory.LatFill.fillSet σ X W v t := by
    rw [GlobalTheory.LatFill.mul_mul_transpose_eq_sum]
    refine sum_mem fun i _ => sum_mem fun j _ => GlobalTheory.LatFill.smul_mem_fillSet (hA i j) ?_
    obtain ⟨y, hy, ey⟩ := (hb _).1 (single_mem i)
    obtain ⟨y', hy', ey'⟩ := (hc _).1 (single_mem j)
    rw [← ey, ← ey']
    exact GlobalTheory.LatFill.vecMulVec_mem_fillSet h hy hy'
  obtain ⟨γ, hγ, h1, h2⟩ := hT
  refine ⟨γ, hγ, Matrix.ext fun i j => h1 i j, ?_⟩
  have e : γ.map (piW t) = b.1 * A * c.1ᵀ := Matrix.ext fun i j => h2 i j
  rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul,
    Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one,
    Matrix.mul_one]
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensorLattice_point_of_integral_splitPlace_coordinate : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ},
    IsCMExt F E σ → ∀ (X : Spc F E n) (W : Spc F E d) (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v))
    (c : GL (Fin d) (Fv F v)), IsSplitBasis t X.L b → IsSplitBasis t W.L c →
    ∀ A : Matrix (Fin n) (Fin d) (Fv F v), (∀ i j, A i j ∈ v.adicCompletionIntegers F) →
      ∃ γ ∈ latAtV X W v, γ.map (piW (t.comp σ)) = 0 ∧ (b⁻¹).1 * γ.map (piW t) * (c⁻¹).1ᵀ = A := by
  first | exact @GlobalTheory.LatFill.exists_latAtV_coord | exact GlobalTheory.LatFill.exists_latAtV_coord | (intros; apply GlobalTheory.LatFill.exists_latAtV_coord <;> assumption)
end

section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.VacLift

theorem exists_lift_scalar {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (v : Pl F) (t : E →ₐ[F] Fv F v) (a : Fv F v) :
    ∃ z : AE F E, At (evFin F v) z ∧ piW (t.comp σ) z = 0 ∧ piW t z = a := by
  have hp : ∀ (s : E →ₐ[F] Fv F v) (z : AE F E), piW s z = splitProj s (compFin F E v z) := fun s z => rfl
  have hs : ∀ (s : E →ₐ[F] Fv F v) (u : AF F) (z : AE F E), piW s (u • z) = evFin F v u * piW s z := by
    intro s u z
    rw [Algebra.smul_def, map_mul]
    congr 1
    rw [hp]
    change splitProj s (TensorProduct.tmul F (evFin F v u) (1 : E)) = _
    rw [splitProj_tmul, map_one, mul_one]
  refine ⟨GlobalTheory.LatVac.liftV v a • Supp.splitIdemAd h t, ?_, ?_, ?_⟩
  · intro u hu
    rw [smul_smul, ← smul_eq_mul u, GlobalTheory.LatVac.at_liftV v a u hu, zero_smul]
  · rw [hs, hp, Supp.splitIdemAd, Supp.compFin_singleTens_self]
    simp [splitIdem]
  · rw [hs, hp, Supp.splitIdemAd, Supp.compFin_singleTens_self, GlobalTheory.LatVac.evFin_liftV]
    simp [splitIdem]

theorem exists_lift : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ},
    IsCMExt F E σ → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
    (Y : Matrix (Fin n) (Fin d) (Fv F v)), ∃ x : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x ∧
      x.map (piW (t.comp σ)) = 0 ∧ (b⁻¹).1 * x.map (piW t) * (c⁻¹).1ᵀ = Y := by
  intro F E _ _ _ _ _ σ n d h v t b c Y
  choose f hf using exists_lift_scalar h v t
  refine ⟨(b.1 * Y * c.1ᵀ).map f, ?_, ?_, ?_⟩
  · intro u hu
    ext i j
    exact (hf _).1 u hu
  · exact Matrix.ext fun i j => (hf _).2.1
  · have e : ((b.1 * Y * c.1ᵀ).map f).map (piW t) = b.1 * Y * c.1ᵀ :=
      Matrix.ext fun i j => (hf _).2.2
    rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
      ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one, Matrix.mul_one]

end GlobalTheory.VacLift
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_supportedAdele_splitPlace_matrix_coordinate_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ},
    IsCMExt F E σ → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
    (Y : Matrix (Fin n) (Fin d) (Fv F v)), ∃ x : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x ∧
      x.map (piW (t.comp σ)) = 0 ∧ (b⁻¹).1 * x.map (piW t) * (c⁻¹).1ᵀ = Y := by
  atlas_forward_decl GlobalTheory.VacLift.exists_lift
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.VacLinW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

theorem symp_eq_zero_of_comp (hcm : IsCMExt F E σ) {v : Pl F} (s : E →ₐ[F] Fv F v)
    {x y : Matrix (Fin n) (Fin d) (AE F E)} (hx : At (evFin F v) x) (hx0 : x.map (piW (s.comp σ)) = 0)
    (hy0 : y.map (piW (s.comp σ)) = 0) (ξ : AE F E) (JA : Matrix (Fin n) (Fin n) (AE F E))
    (JB : Matrix (Fin d) (Fin d) (AE F E)) : symp (cA σ) ξ JA JB x y = 0 := by
  set z := hTens (cA σ) JA JB x y with hz
  have hat : At (evFin F v) z := by
    intro c hc
    have hij : ∀ i j, c • x i j = 0 := fun i j => by
      have := congrFun (congrFun (hx c hc) i) j
      simpa using this
    simp only [hz, hTens, Finset.smul_sum, ← smul_mul_assoc, hij, zero_mul, Finset.sum_const_zero]
  have hx' : ∀ i j, piW (s.comp σ) (x i j) = 0 := fun i j => by simpa using congrFun (congrFun hx0 i) j
  have hy' : ∀ i j, piW (s.comp σ) (y i j) = 0 := fun i j => by simpa using congrFun (congrFun hy0 i) j
  have h1 : piW s z = 0 := by
    simp only [hz, hTens, map_sum, map_mul, GlobalTheory.VacIso.piW_cA, hy', mul_zero, Finset.sum_const_zero]
  have h2 : piW (s.comp σ) z = 0 := by
    simp only [hz, hTens, map_sum, map_mul, hx', zero_mul, Finset.sum_const_zero]
  have : z = 0 := GlobalTheory.VacIso.eq_zero_of_at_split hcm s hat h1 h2
  simp only [symp, ← hz, this, mul_zero, map_zero]

theorem symp_add_right (ξ : AE F E) (JA : Matrix (Fin n) (Fin n) (AE F E)) (JB : Matrix (Fin d) (Fin d) (AE F E))
    (x y y' : Matrix (Fin n) (Fin d) (AE F E)) :
    symp (cA σ) ξ JA JB x (y + y') = symp (cA σ) ξ JA JB x y + symp (cA σ) ξ JA JB x y' := by
  simp only [symp, hTens, Matrix.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem isLin_smul {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) {v : Pl F}
    {π₁ π₀ : AE F E →+* Fv F v} {co : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n) (Fin d) (Fv F v)}
    {ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) (Fv F v) → ℂ)} (h : M.IsLin ψ π₁ π₀ co ι)
    {z : ℂ} (hz : z ≠ 0) : M.IsLin ψ π₁ π₀ co (z • ι) where
  bij := by
    refine ⟨fun φ hφ => ?_, fun φ hφ φ' hφ' e => ?_, fun g hg => ?_⟩
    · simp only [LinearMap.smul_apply]; exact Submodule.smul_mem _ z (h.bij.mapsTo hφ)
    · simp only [LinearMap.smul_apply] at e
      exact h.bij.injOn hφ hφ' (smul_right_injective _ hz e)
    · obtain ⟨φ, hφ, e⟩ := h.bij.surjOn (Submodule.smul_mem _ z⁻¹ hg)
      refine ⟨φ, hφ, ?_⟩
      simp only [LinearMap.smul_apply, e, smul_smul, mul_inv_cancel₀ hz, one_smul]
  trans := fun u hu h0 φ hφ φ₁ hφ₁ hA Y => by
    simp only [LinearMap.smul_apply, Pi.smul_apply, h.trans u hu h0 φ hφ φ₁ hφ₁ hA Y]
  mult := fun u hu h1 φ hφ φ₁ hφ₁ hA x hx hx0 => by
    simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, h.mult u hu h1 φ hφ φ₁ hφ₁ hA x hx hx0]
    ring

theorem vac_linW : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), IsSplitBasis t X.L b → IsSplitBasis t W.L c →
    ∃ ι, M.IsLinW B.ψ t b c ι ∧ ι (M.vac v) = Set.indicator {Y | ∀ i j, Y i j ∈ v.adicCompletionIntegers F} 1 := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair v t b c hb hc
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_linear_witt_model_local hP F E σ B n d X W M χX χW om r s r' s' hPair v t b c
  have hcm : IsCMExt F E σ := hPair.base.cm
  obtain ⟨hSB, hne, θ, -, hfix⟩ := hPair.good.vac v
  have hat := (GlobalTheory.LatVac.latAtV_at_stable X W v).1
  have htt : (t.comp σ).comp σ = t := GlobalTheory.AdelicU.comp_conj_conj hcm t

  have hfix' : ∀ γ ∈ latAtV X W v, (γ.map (piW (t.comp σ)) = 0 ∨ γ.map (piW t) = 0) →
      Acts (evFin F v) (M.co.rho B.ψ γ) (M.vac v) (M.vac v) := by
    intro γ hγ h
    have h0 : symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ = 0 := by
      rcases h with h | h
      · exact symp_eq_zero_of_comp hcm t (hat γ hγ) h h _ _ _
      · rw [← htt] at h
        exact symp_eq_zero_of_comp hcm (t.comp σ) (hat γ hγ) h h _ _ _
    have := hfix γ hγ
    rwa [h0, mul_zero, AddChar.map_zero_eq_one, one_smul] at this
  set f := ι (M.vac v) with hf
  set S : Set (Matrix (Fin n) (Fin d) (Fv F v)) := {Y | ∀ i j, Y i j ∈ v.adicCompletionIntegers F} with hS

  have htr : ∀ A ∈ S, ∀ Y, f (Y + A) = f Y := by
    intro A hA Y
    obtain ⟨γ, hγ, h0, hco⟩ := GlobalTheory.T.exists_tensorLattice_point_of_integral_splitPlace_coordinate hcm X W v t b c hb hc A hA
    have := hι.trans γ (hat γ hγ) h0 _ hSB _ hSB (hfix' γ hγ (Or.inl h0)) Y
    rw [hco] at this
    exact this.symm

  have hsupp : ∀ Y, f Y ≠ 0 → Y ∈ S := by
    intro Y hY
    obtain ⟨x, hx, hx0, rfl⟩ := GlobalTheory.T.exists_supportedAdele_splitPlace_matrix_coordinate_eq hcm v t b c Y
    have hψ : ∀ u ∈ latAtV X W v, u.map (piW t) = 0 →
        B.ψ (symp (cA σ) (-1) (incM F X.J) (incM F W.J) x u) = 1 := by
      intro u hu hu0
      have hm := hι.mult u (hat u hu) hu0 _ hSB _ hSB (hfix' u hu (Or.inr hu0)) x hx hx0
      exact (mul_eq_right₀ hY).mp hm.symm
    have hmem : x ∈ latAtV X W v := by
      refine (GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B n d X W r s r' s' hPair.base hPair.herm hPair.skew v x hx).2
        fun γ hγ => ?_
      obtain ⟨γ₁, hγ₁, γ₂, hγ₂, rfl, h₁, h₂⟩ := GlobalTheory.T.tensorLatticeAtFinitePlace_eq_sum_splitPlace_parts hcm X W v t γ hγ
      rw [symp_add_right, symp_eq_zero_of_comp hcm t hx hx0 h₁, zero_add]
      exact hψ γ₂ hγ₂ h₂
    exact GlobalTheory.T.splitPlace_tensorLattice_component_integral X W v t b c hb hc x hmem
  have hf0 : f ≠ 0 := by
    intro h
    apply hne
    refine hι.bij.injOn hSB (zero_mem _) ?_
    rw [map_zero]; exact h
  have hfe : f = f 0 • S.indicator 1 := by
    funext Y
    by_cases hY : Y ∈ S
    · rw [Pi.smul_apply, Set.indicator_of_mem hY, Pi.one_apply, smul_eq_mul, mul_one, ← htr Y hY 0, zero_add]
    · rw [Pi.smul_apply, Set.indicator_of_notMem hY, smul_zero]
      by_contra h
      exact hY (hsupp Y h)
  have hz : f 0 ≠ 0 := by
    intro h
    apply hf0
    rw [hfe, h, zero_smul]
  refine ⟨(f 0)⁻¹ • ι, isLin_smul M B.ψ hι (inv_ne_zero hz), ?_⟩
  rw [LinearMap.smul_apply, ← hf]
  exact (congrArg ((f 0)⁻¹ • ·) hfe).trans (by rw [smul_smul, inv_mul_cancel₀ hz, one_smul])

end GlobalTheory.VacLinW
end
end
