import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenKer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NEqAndIsClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasureFundamentalDomainLtTop

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.BesselData (hA vecA actV)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeisCoord

open GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices (gramA gramInvA)
open Matrix

variable {D : D7}

theorem dot_cT {R : Type} [CommRing R] (σ : R →+* R) {n m : ℕ} (P : Matrix (Fin n) (Fin m) R) (y : Fin m → R)
    (v : Fin n → R) : (fun i => σ ((P *ᵥ y) i)) ⬝ᵥ v = (fun i => σ (y i)) ⬝ᵥ (Formalism.UG.cT σ P *ᵥ v) := by
  rw [← BesselChar.mulVec_map, Formalism.UG.cT, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem cancel_gen {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} {H H' J J' : Matrix (Fin n) (Fin n) R}
    (hH : H * H' = 1) (hJ : J' * J = 1) {v w : Fin n → R}
    (h : Formalism.UG.cT σ H *ᵥ (J *ᵥ v) = Formalism.UG.cT σ H *ᵥ (J *ᵥ w)) : v = w := by
  have h3 : J' * Formalism.UG.cT σ H' * Formalism.UG.cT σ H * J = 1 := by
    rw [Matrix.mul_assoc J', ← Formalism.UG.cT_mul, hH, Formalism.UG.cT_one, Matrix.mul_one, hJ]
  have h4 : ∀ u, (J' * Formalism.UG.cT σ H') *ᵥ (Formalism.UG.cT σ H *ᵥ (J *ᵥ u)) = u := fun u => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h3, Matrix.one_mulVec]
  rw [← h4 v, h, h4]

theorem hA_dot (B : HSp D) (x y : Fin B.rank → AE D) : hA B x y = (fun i => cA D (y i)) ⬝ᵥ (gramA B *ᵥ x) := by
  simp only [hA, dotProduct, Matrix.mulVec, gramA, Matrix.map_apply, Finset.mul_sum, mul_assoc]

theorem mt_unitary (B : HSp D) (g : GA D B) :
    Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt B g) * gramA B * Formalism.L2.Theta.mt B g = gramA B := g.2

theorem hA_mt (B : HSp D) (g : GA D B) (x y : Fin B.rank → AE D) :
    hA B (Formalism.L2.Theta.mt B g *ᵥ x) (Formalism.L2.Theta.mt B g *ᵥ y) = hA B x y := by
  rw [hA_dot, hA_dot, dot_cT, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mt_unitary]

theorem exists_rat {B : HSp D} {γ : GA D B} (hγ : γ ∈ GQ B) (x : B.V) : ∃ x', actV B γ x = vecA B x' := by
  obtain ⟨γ', -, h⟩ := hγ
  have hm : Formalism.L2.Theta.mt B γ = (γ' : Matrix (Fin B.rank) (Fin B.rank) D.host.E).map (incA D) :=
    (congrArg Units.val h).symm
  obtain ⟨v, hv⟩ := BesselCompare.co_surj B
    ((γ' : Matrix (Fin B.rank) (Fin B.rank) D.host.E) *ᵥ BesselCompare.co B x)
  refine ⟨v, ?_⟩
  have := BesselChar.mulVec_map (incA D) (γ' : Matrix (Fin B.rank) (Fin B.rank) D.host.E) (BesselCompare.co B x)
  rw [← hv] at this
  unfold actV
  rw [hm]
  exact this

theorem exists_rat_hA {B : HSp D} {γ : GA D B} (hγ : γ ∈ GQ B) (x y : B.V) :
    ∃ s, hA B (actV B γ x) (vecA B y) = incA D s := by
  obtain ⟨x', h⟩ := exists_rat hγ x
  exact ⟨_, by rw [h, BesselCompare.hA_vec]⟩

theorem continuous_hA (B : HSp D) (x y : B.V) : Continuous fun n : GA D B => hA B (actV B n x) (vecA B y) := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have hm0 : Continuous (fun k : GA D B => Formalism.L2.Theta.mt B k) := Units.continuous_val.comp continuous_subtype_val
  have h1 : Continuous fun n : GA D B => actV B n x := hm0.matrix_mulVec continuous_const
  unfold hA
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_const.mul ((continuous_apply j).comp h1)

variable {L A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem chr_rat (d : FJDat L A B ι) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {γ : GA D B}
    (hγ : γ ∈ GQ B) : d.chr ψ γ = 1 := by
  choose s hs using exists_rat_hA hγ
  unfold FJDat.chr
  simp only [hs, ← map_mul, ← map_sum]
  rw [BesselChar.trace_incA]
  exact hψ.2.2.1 _

theorem jac_rat (d : FJDat L A B ι) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {γ : GA D B}
    (hγ : γ ∈ GQ B) {f : WA L A → ℂ} (hf : IsThetaFun ψ L A f) : d.jac ψ γ f 0 = f 0 := by
  choose s hs using exists_rat_hA hγ
  have h1 : ψ (cenCo L d.c (d.tCo γ)) = 1 := by
    unfold cenCo FJDat.tCo
    rw [hs, ← map_mul, BesselChar.trace_incA, ← map_mul]
    exact hψ.2.2.1 _
  have h2 : d.aCo γ = fun i => incA D ((A.gram⁻¹ *ᵥ fun k => s d.fTop (ι (A.frame k))) i) := by
    unfold FJDat.aCo gramInvA
    simp only [hs]
    exact BesselChar.mulVec_map _ _ _
  have h3 : tPt L A d.c (d.aCo γ) =
      ratW L A (Matrix.of fun _ i => -(d.c * (A.gram⁻¹ *ᵥ fun k => s d.fTop (ι (A.frame k))) i)) := by
    rw [h2]
    ext i k
    change -(incA D _ * incA D _) = incA D (-(_ * _))
    rw [map_neg, map_mul]
  have h4 : ∀ w : WA L A, symplH L A w 0 = 0 := fun w => by
    have := DualPairCheck.symplH_add_right L A w 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  have h5 := hf.quasi (Matrix.of fun _ i => -(d.c * (A.gram⁻¹ *ᵥ fun k => s d.fTop (ι (A.frame k))) i)) 0
  rw [h4, neg_zero, AddChar.map_zero_eq_one, one_mul, add_zero, ← h3] at h5
  have h6 := d.theta_eq ψ (fun _ => f) γ 1
  rw [h1, one_mul, h5] at h6
  exact h6

theorem continuous_chr (d : FJDat L A B ι) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) :
    Continuous (d.chr ψ) := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  exact hψ.1.comp (ht.comp (continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_hA B _ _)))

theorem continuous_aCo (d : FJDat L A B ι) : Continuous d.aCo := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  exact (continuous_const (y := gramInvA A)).matrix_mulVec (continuous_pi fun i => continuous_hA B _ _)

theorem fix_of_perp {g : GA D B} {h : GA D A} (hg : EmbRel B A ι g h) {v : B.V} (hv : ∀ x, B.hD v (ι x) = 0) :
    Formalism.L2.Theta.mt B g *ᵥ vecA B v = vecA B v := by
  refine hg.2 (BesselCompare.co B v) ?_
  funext i
  rw [BesselCompare.frameMat_eq, BesselCompare.cT_mulVec]
  exact hv _

theorem actV_conj {g : GA D B} (n : GA D B) {v : B.V} (hv : Formalism.L2.Theta.mt B g *ᵥ vecA B v = vecA B v) :
    actV B (g * n * g⁻¹) v = Formalism.L2.Theta.mt B g *ᵥ actV B n v := by
  unfold actV
  rw [BesselChar.mt_mul, BesselChar.mt_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    BesselChar.inv_fix_vec (BesselChar.mt_inv_mul B g) hv]

theorem hA_conj {g : GA D B} (n : GA D B) {v w : B.V} (hv : Formalism.L2.Theta.mt B g *ᵥ vecA B v = vecA B v)
    (hw : Formalism.L2.Theta.mt B g *ᵥ vecA B w = vecA B w) :
    hA B (actV B (g * n * g⁻¹) v) (vecA B w) = hA B (actV B n v) (vecA B w) := by
  rw [actV_conj n hv]
  conv_lhs => rw [← hw]
  exact hA_mt B g _ _

theorem gram_aCo (d : FJDat L A B ι) (n : GA D B) : gramA A *ᵥ d.aCo n =
    Formalism.UG.cT (cA D) ((frameMat B A ι).map (incA D)) *ᵥ (gramA B *ᵥ actV B n d.fTop) := by
  unfold FJDat.aCo
  rw [Matrix.mulVec_mulVec, WeilTieCompare.gram_mul_inv, Matrix.one_mulVec, BesselCompare.frameMat_eq]
  funext i
  rw [hA_dot]
  rfl

theorem aCo_conj (d : FJDat L A B ι) {g : GA D B} {h : GA D A} (hg : EmbRel B A ι g h) (n : GA D B) :
    d.aCo (g * n * g⁻¹) = Formalism.L2.Theta.mt A h *ᵥ d.aCo n := by
  have hf := fix_of_perp hg fun x => d.hD_fTop _ fun i => d.fA i x
  have h1 : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt B g * (frameMat B A ι).map (incA D)) =
      Formalism.UG.cT (cA D) ((frameMat B A ι).map (incA D) * Formalism.L2.Theta.mt A h) := congrArg _ hg.1
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul] at h1
  have h2 : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt A h) *ᵥ (gramA A *ᵥ d.aCo (g * n * g⁻¹)) =
      Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt A h) *ᵥ (gramA A *ᵥ (Formalism.L2.Theta.mt A h *ᵥ d.aCo n)) := by
    rw [gram_aCo, Matrix.mulVec_mulVec, ← h1, ← Matrix.mulVec_mulVec, actV_conj n hf,
      Matrix.mulVec_mulVec _ _ (gramA B), Matrix.mulVec_mulVec _ _ (Formalism.L2.Theta.mt B g), mt_unitary, ← gram_aCo,
      Matrix.mulVec_mulVec _ _ (gramA A), Matrix.mulVec_mulVec _ _ (Formalism.L2.Theta.mt A h), mt_unitary]
  exact cancel_gen (cA D) (BesselChar.mt_mul_inv A h) (WeilTieCompare.inv_mul_gram A) h2

theorem conj_mem (d : FJDat L A B ι) {g : GA D B} {h : GA D A} (hg : EmbRel B A ι g h) {n : GA D B} (hn : n ∈ d.N) :
    g * n * g⁻¹ ∈ d.N := by
  have he : HMul.hMul (Formalism.L2.Theta.mt B g) (d.eM.map (incA D)) = d.eM.map (incA D) := by
    ext k i
    exact congr_fun (fix_of_perp hg (d.eA i)) k
  have he' := BesselChar.inv_fix_cols (BesselChar.mt_inv_mul B g) he
  rw [FJDat.N, BesselChar.mem_NFlag_iff B d.eM d.isIsoSub.1] at hn ⊢
  rw [BesselChar.mt_mul, BesselChar.mt_mul]
  exact hn.conj he he' (BesselChar.mt_mul_inv B g) (BesselChar.perp_fixed d.eM g⁻¹ he')

theorem coords_laws : ∀ (D : D7) (L A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : FJDat L A B ι), (∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ → (∀ γ ∈ GQ B, d.chr ψ γ = 1 ∧ ∀ f, IsThetaFun ψ L A f → d.jac ψ γ f 0 = f 0) ∧ Continuous (d.chr ψ)) ∧ Continuous d.aCo ∧ Continuous d.tCo ∧ ∀ g h, EmbRel B A ι g h → ∀ n ∈ d.N, g * n * g⁻¹ ∈ d.N ∧ d.aCo (g * n * g⁻¹) = (Formalism.L2.Theta.mt A h).mulVec (d.aCo n) ∧ d.tCo (g * n * g⁻¹) = d.tCo n ∧ ∀ ψ : AddChar (AF D.host.F) ℂ, d.chr ψ (g * n * g⁻¹) = d.chr ψ n := by
  intro D L A B ι d
  refine ⟨fun ψ hψ => ⟨fun γ hγ => ⟨chr_rat d hψ hγ, fun f hf => jac_rat d hψ hγ hf⟩, continuous_chr d hψ⟩,
    continuous_aCo d, continuous_hA B _ _, fun g h hg n hn => ⟨conj_mem d hg hn, aCo_conj d hg n, ?_, fun ψ => ?_⟩⟩
  · have hf := fix_of_perp hg fun x => d.hD_fTop _ fun i => d.fA i x
    exact hA_conj n hf hf
  · unfold FJDat.chr
    simp only [hA_conj n (fix_of_perp hg (d.eA _)) (fix_of_perp hg (d.fA _))]

end GlobalTheory.HeisCoord

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.BesselData (hA vecA actV)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_unipotent_conjugation : ∀ (D : D7) (L A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : FJDat L A B ι), (∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ → (∀ γ ∈ GQ B, d.chr ψ γ = 1 ∧ ∀ f, IsThetaFun ψ L A f → d.jac ψ γ f 0 = f 0) ∧ Continuous (d.chr ψ)) ∧ Continuous d.aCo ∧ Continuous d.tCo ∧ ∀ g h, EmbRel B A ι g h → ∀ n ∈ d.N, g * n * g⁻¹ ∈ d.N ∧ d.aCo (g * n * g⁻¹) = (Formalism.L2.Theta.mt A h).mulVec (d.aCo n) ∧ d.tCo (g * n * g⁻¹) = d.tCo n ∧ ∀ ψ : AddChar (AF D.host.F) ℂ, d.chr ψ (g * n * g⁻¹) = d.chr ψ n := by
  first | exact @GlobalTheory.HeisCoord.coords_laws | exact GlobalTheory.HeisCoord.coords_laws | (intros; apply GlobalTheory.HeisCoord.coords_laws <;> assumption)
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.BesselData (hA vecA actV)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeisLaw

open GlobalTheory.BesselCompare GlobalTheory.RootExch GlobalTheory.BesselClosed

variable {D : D7} {L A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem rat_decomp (d : FJDat L A B ι) (v : B.V) :
    ∃ (c : Fin d.ρ → D.host.E) (a : A.V) (c' : Fin d.ρ → D.host.E), v = ∑ l, c l • d.e l + ι a + ∑ l, c' l • d.f l := by
  let Φ : ((Fin d.ρ → D.host.E) × A.V × (Fin d.ρ → D.host.E)) →ₗ[D.host.E] B.V :=
    (Fintype.linearCombination D.host.E d.e).coprod (ι.coprod (Fintype.linearCombination D.host.E d.f))
  have hΦ : ∀ c a c', Φ (c, a, c') = ∑ l, c l • d.e l + ι a + ∑ l, c' l • d.f l := fun c a c' => by
    simp [Φ, Fintype.linearCombination_apply, add_assoc]
  have sw : ∀ x y : B.V, B.hT y x = star (B.hT x y) := fun x y => (B.herm.eq _ _).symm
  have ef : ∀ i l, B.hT (d.f i) (d.e l) = if l = i then 1 else 0 := fun i l => d.ef l i
  have fe : ∀ i l, B.hT (d.e i) (d.f l) = if l = i then 1 else 0 := fun i l => by
    rw [sw, ef]; by_cases h : i = l
    · simp [h]
    · simp [h, Ne.symm h]
  have ee : ∀ i l, B.hT (d.e i) (d.e l) = 0 := fun i l => d.ee l i
  have ff : ∀ i l, B.hT (d.f i) (d.f l) = 0 := fun i l => d.ff l i
  have eA : ∀ i x, B.hT (d.e i) (ι x) = 0 := fun i x => hD_swap_zero (d.eA i x)
  have fA : ∀ i x, B.hT (d.f i) (ι x) = 0 := fun i x => hD_swap_zero (d.fA i x)
  have hinj : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 ?_
    rintro ⟨c, a, c'⟩ h
    rw [hΦ] at h
    have h1 : c = 0 := funext fun i => by simpa [map_sum, ef, ff, fA] using congrArg (B.hT (d.f i)) h
    have h2 : c' = 0 := funext fun i => by simpa [map_sum, fe, ee, eA] using congrArg (B.hT (d.e i)) h
    subst h1 h2
    have h3 : ι a = 0 := by simpa using h
    have h4 : a = 0 := A.nondeg.1 a fun y => by rw [← d.isom a y, h3]; simp
    rw [h4]; rfl
  have := Module.Finite.of_basis A.frame
  have := Module.Finite.of_basis B.frame
  have hs : Function.Surjective Φ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
    have := d.codim
    simp only [Module.finrank_prod, Module.finrank_fin_fun, A.rank_eq, B.rank_eq]
    omega)).1 hinj
  obtain ⟨⟨c, a, c'⟩, h⟩ := hs v
  exact ⟨c, a, c', by rw [← h, hΦ]⟩

theorem vecA_add (v w : B.V) : vecA B (v + w) = vecA B v + vecA B w := by
  funext k; simp [vecA]

theorem vecA_sum {ρ : ℕ} (c : Fin ρ → D.host.E) (e : Fin ρ → B.V) :
    vecA B (∑ l, c l • e l) = ∑ l, incA D (c l) • vecA B (e l) := by
  funext k; simp [vecA, map_sum]

theorem iA_eq (s : Fin A.rank → AE D) : iA ι s = ∑ l, s l • vecA B (ι (A.frame l)) := by
  rw [iA, frameMat_eq, eMat_mulVec]

theorem vecA_iota (a : A.V) : vecA B (ι a) = iA ι (vecA A a) := by
  rw [iA_eq]
  conv_lhs => rw [← A.frame.sum_repr a]
  simp only [map_sum, map_smul]
  rw [vecA_sum]
  rfl

theorem eq_sum_frame (x : Fin B.rank → AE D) : x = ∑ k, x k • vecA B (B.frame k) := by
  funext j
  simp [vecA, Finsupp.single_apply, apply_ite (incA D)]

theorem ad_decomp (d : FJDat L A B ι) (x : Fin B.rank → AE D) :
    ∃ (c : Fin d.ρ → AE D) (a : Fin A.rank → AE D) (c' : Fin d.ρ → AE D),
      x = ∑ l, c l • vecA B (d.e l) + iA ι a + ∑ l, c' l • vecA B (d.f l) := by
  let Φ : ((Fin d.ρ → AE D) × (Fin A.rank → AE D) × (Fin d.ρ → AE D)) →ₗ[AE D] (Fin B.rank → AE D) :=
    (Fintype.linearCombination (AE D) fun l => vecA B (d.e l)).coprod
      (((frameMat B A ι).map (incA D)).mulVecLin.coprod (Fintype.linearCombination (AE D) fun l => vecA B (d.f l)))
  have hΦ : ∀ c a c', Φ (c, a, c') = ∑ l, c l • vecA B (d.e l) + iA ι a + ∑ l, c' l • vecA B (d.f l) := fun c a c' => by
    simp only [Φ, LinearMap.coprod_apply, Fintype.linearCombination_apply, add_assoc, Matrix.mulVecLin_apply, iA]
  have hx : x ∈ LinearMap.range Φ := by
    rw [eq_sum_frame x]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    obtain ⟨c, a, c', h⟩ := rat_decomp d (B.frame k)
    refine ⟨(fun l => incA D (c l), vecA A a, fun l => incA D (c' l)), ?_⟩
    rw [hΦ, h, vecA_add, vecA_add, vecA_sum, vecA_sum, vecA_iota]
  obtain ⟨⟨c, a, c'⟩, h⟩ := hx
  exact ⟨c, a, c', by rw [← h, hΦ]⟩

variable (d : FJDat L A B ι)

theorem mem_NS {n : GA D B} (hn : n ∈ d.N) : n ∈ NS B d.e := by
  rw [← closure_NS, SetLike.mem_coe, ← NFlag_eMat]; exact hn

theorem lower {n : GA D B} (hn : n ∈ d.N) {k : ℕ} {v} (hv : v ∈ spanLt B d.e (k + 1)) :
    (mt B n).mulVec v - v ∈ spanLt B d.e k := by
  obtain ⟨c, hc, rfl⟩ := hv
  rw [← Matrix.mulVecLin_apply, map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [map_smul, ← smul_sub]
  rcases lt_or_ge l.1 (k + 1) with hl | hl
  · exact Submodule.smul_mem _ _ (spanLt_mono (by omega) ((mem_NS_iff.1 (mem_NS d hn)).1 l))
  · rw [hc l hl, zero_smul]; exact zero_mem _

theorem lower_iA {n : GA D B} (hn : n ∈ d.N) (a) : (mt B n).mulVec (iA ι a) - iA ι a ∈ spanLt B d.e d.ρ := by
  rw [iA_eq, ← Matrix.mulVecLin_apply, map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [map_smul, ← smul_sub]
  exact Submodule.smul_mem _ _ ((mem_NS_iff.1 (mem_NS d hn)).2 _ fun i => hD_swap_zero (d.eA i _))

theorem hA_zero_swap {x y : Fin B.rank → AE D} (h : hA B x y = 0) : hA B y x = 0 := by
  rw [← hA_herm, h, map_zero]

theorem hA_span_of {k : ℕ} {v y} (hv : v ∈ spanLt B d.e k) (h : ∀ l : Fin d.ρ, l.1 < k → hA B (vecA B (d.e l)) y = 0) :
    hA B v y = 0 := by
  obtain ⟨c, hc, rfl⟩ := hv
  rw [hA_sum]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [hA_smul]
  rcases lt_or_ge l.1 k with hl | hl
  · rw [h l hl, mul_zero]
  · rw [hc l hl, zero_mul]

theorem hA_span_iA {k : ℕ} {v} (hv : v ∈ spanLt B d.e k) (a) : hA B v (iA ι a) = 0 :=
  hA_span_of d hv fun l _ => hA_vec_iA (d.eA l) a

theorem hA_span_span {k k' : ℕ} {v w} (hv : v ∈ spanLt B d.e k) (hw : w ∈ spanLt B d.e k') : hA B v w = 0 :=
  hA_span_of d hv fun l _ => hA_zero_swap (hA_span_of d hw fun j _ => by rw [hA_vec, d.ee, map_zero])

theorem hD_e_fTop (l : Fin d.ρ) : B.hD (d.e l) d.fTop = if l.1 + 1 = d.ρ then 1 else 0 := by
  have ef : ∀ i, B.hT (d.f i) (d.e l) = if l = i then 1 else 0 := fun i => d.ef l i
  unfold HSpace.hD
  rw [FJDat.fTop, map_sum, LinearMap.sum_apply, Finset.sum_eq_single l]
  · split_ifs
    · rw [ef, if_pos rfl]
    · rw [map_zero, LinearMap.zero_apply]
  · intro i _ hi
    split_ifs
    · rw [ef, if_neg hi.symm]
    · rw [map_zero, LinearMap.zero_apply]
  · exact fun hl => absurd (Finset.mem_univ l) hl

theorem hA_span_fTop {v} (hv : v ∈ spanLt B d.e (d.ρ - 1)) : hA B v (vecA B d.fTop) = 0 :=
  hA_span_of d hv fun l hl => by rw [hA_vec, hD_e_fTop, if_neg (by omega), map_zero]

theorem hA_fTop_iA (a) : hA B (vecA B d.fTop) (iA ι a) = 0 :=
  hA_vec_iA (fun x => d.hD_fTop _ fun l => d.fA l x) a

theorem hA_fTop_fTop : hA B (vecA B d.fTop) (vecA B d.fTop) = 0 := by
  rw [hA_vec, d.hD_fTop _ fun i => hD_swap_zero (d.hD_fTop _ fun j => d.ff j i), map_zero]

theorem vecA_fTop : vecA B d.fTop = ∑ l : Fin d.ρ, (if l.1 + 1 = d.ρ then (1 : AE D) else 0) • vecA B (d.f l) := by
  have : d.fTop = ∑ l : Fin d.ρ, (if l.1 + 1 = d.ρ then (1 : D.host.E) else 0) • d.f l :=
    Finset.sum_congr rfl fun l _ => by split_ifs <;> simp
  rw [this, vecA_sum]
  exact Finset.sum_congr rfl fun l _ => by split_ifs <;> simp

theorem sum_mem_span (b : Fin d.ρ → AE D) : ∑ l, b l • vecA B (d.e l) ∈ spanLt B d.e d.ρ :=
  ⟨b, fun l hl => absurd l.2 (by omega), rfl⟩

theorem act_fTop {n : GA D B} (hn : n ∈ d.N) : ∃ b : Fin d.ρ → AE D,
    actV B n d.fTop = vecA B d.fTop + iA ι (d.aCo n) + ∑ l, b l • vecA B (d.e l) := by
  obtain ⟨c, a, c', h⟩ := ad_decomp d (actV B n d.fTop)
  have fe : ∀ i j, B.hD (d.f i) (d.e j) = if i = j then 1 else 0 := fun i j => by
    have h1 : B.hD (d.f i) (d.e j) = star (B.hD (d.e j) (d.f i)) := (B.herm.eq _ _).symm
    rw [h1, d.ef]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  have hc : ∀ j : Fin d.ρ, c' j = if j.1 + 1 = d.ρ then 1 else 0 := fun j => by
    have h1 : hA B (actV B n d.fTop) (vecA B (d.e j)) = c' j := by
      rw [h, hA_add, hA_add, hA_coeff B d.f d.e fe, hA_zero_swap (hA_vec_iA (d.eA j) a),
        hA_span_span d (sum_mem_span d c) (vec_mem_spanLt j.2), zero_add, zero_add]
    have h2 := hA_span_fTop d (spanLt_mono (by have := j.2; omega)
      (lower d (inv_mem hn) (vec_mem_spanLt (B := B) (e := d.e) (l := j) (Nat.lt_succ_self _))))
    rw [hA_sub, sub_eq_zero, hA_vec, hD_e_fTop] at h2
    rw [← h1, actV, hA_mt_left, ← hA_herm, h2]
    split_ifs <;> simp
  have h' : actV B n d.fTop = vecA B d.fTop + iA ι a + ∑ l, c l • vecA B (d.e l) := by
    rw [h, vecA_fTop]; simp only [hc]; abel
  exact ⟨c, by rw [(d.coords_of n a c h').1]; exact h'⟩

theorem span_pred {n : GA D B} (hn : n ∈ d.N) {v} (hv : v ∈ spanLt B d.e d.ρ) :
    (mt B n).mulVec v - v ∈ spanLt B d.e (d.ρ - 1) :=
  lower d hn (spanLt_mono (by omega) hv)

theorem aCo_mul {n n' : GA D B} (hn : n ∈ d.N) (hn' : n' ∈ d.N) : d.aCo (n * n') = d.aCo n + d.aCo n' := by
  obtain ⟨b, h⟩ := act_fTop d hn
  obtain ⟨b', h'⟩ := act_fTop d hn'
  obtain ⟨c, -, hc⟩ := add_mem (add_mem (sum_mem_span d b) (lower_iA d hn (d.aCo n')))
    (add_mem (spanLt_mono (Nat.sub_le _ _) (span_pred d hn (sum_mem_span d b'))) (sum_mem_span d b'))
  refine (d.coords_of _ _ c ?_).1
  change _ = _ + iA ι _ + _
  unfold actV at h h' ⊢
  rw [mulVec_mul, h', Matrix.mulVec_add, Matrix.mulVec_add, h, ← hc, iA_add]
  abel

theorem tCo_mul {n n' : GA D B} (hn : n ∈ d.N) (hn' : n' ∈ d.N) :
    d.tCo (n * n') = d.tCo n + d.tCo n' - hA A (d.aCo n') (d.aCo n) := by
  obtain ⟨b, h⟩ := act_fTop d hn
  obtain ⟨b', h'⟩ := act_fTop d hn'
  have hs := lower_iA d hn (d.aCo n')
  have h1 := hA_span_fTop d (span_pred d hn (sum_mem_span d b'))
  rw [hA_sub, sub_eq_zero] at h1
  have h2 : d.tCo n' = hA B (∑ l, b' l • vecA B (d.e l)) (vecA B d.fTop) := by
    rw [FJDat.tCo, h', hA_add, hA_add, hA_fTop_fTop, hA_zero_swap (hA_fTop_iA d _), zero_add, zero_add]
  have h3 := hA_mt n (iA ι (d.aCo n')) (vecA B d.fTop)
  have h4 := hA_span_iA d hs (d.aCo n)
  have h5 := hA_span_span d hs (sum_mem_span d b)
  rw [hA_sub, sub_eq_zero] at h4 h5
  rw [hA_iA d.isom] at h4
  rw [hA_zero_swap (hA_span_iA d (sum_mem_span d b) _)] at h5
  unfold actV at h
  rw [h, hA_add_right, hA_add_right, h4, h5, hA_zero_swap (hA_fTop_iA d _)] at h3
  have h6 : d.tCo (n * n') = d.tCo n + hA B ((mt B n).mulVec (iA ι (d.aCo n'))) (vecA B d.fTop) + d.tCo n' := by
    unfold actV at h'
    rw [h2, ← h1, FJDat.tCo, FJDat.tCo, actV, actV, mulVec_mul, h', Matrix.mulVec_add, Matrix.mulVec_add, hA_add, hA_add]
  linear_combination h6 + h3

theorem simple_mul {n n' : GA D B} (hn : n ∈ d.N) (hn' : n' ∈ d.N) (i j : Fin d.ρ) (hij : j.1 = i.1 + 1) :
    hA B (actV B (n * n') (d.e j)) (vecA B (d.f i)) =
      hA B (actV B n (d.e j)) (vecA B (d.f i)) + hA B (actV B n' (d.e j)) (vecA B (d.f i)) := by
  have h1 := (mem_NS_iff.1 (mem_NS d hn')).1 j
  rw [hij] at h1
  have h2 := ((mem_spanLt_iff d.ef).1 (lower d hn h1)).1 i le_rfl
  rw [hA_sub, hA_sub, hA_vec, d.ef, if_neg (fun e => by subst e; omega), map_zero, Matrix.mulVec_sub, hA_sub] at h2
  unfold actV at h2 ⊢
  rw [mulVec_mul]
  linear_combination h2

theorem chr_mul {n n' : GA D B} (hn : n ∈ d.N) (hn' : n' ∈ d.N) (ψ : AddChar (AF D.host.F) ℂ) :
    d.chr ψ (n * n') = d.chr ψ n * d.chr ψ n' := by
  unfold FJDat.chr
  rw [← AddChar.map_add_eq_mul, ← map_add, ← Finset.sum_add_distrib]
  congr 2
  exact Finset.sum_congr rfl fun i _ => by rw [simple_mul d hn hn' _ _ rfl, mul_add]

theorem law : ∀ (D : D7) (L A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : FJDat L A B ι), ∀ n ∈ d.N, ∀ n' ∈ d.N,
    d.aCo (n * n') = d.aCo n + d.aCo n' ∧ d.tCo (n * n') = d.tCo n + d.tCo n' - hA A (d.aCo n') (d.aCo n) ∧
    (∀ ψ : AddChar (AF D.host.F) ℂ, d.chr ψ (n * n') = d.chr ψ n * d.chr ψ n') ∧
    ∃ b : Fin d.ρ → AE D, actV B n d.fTop =
      vecA B d.fTop + ((frameMat B A ι).map (incA D)).mulVec (d.aCo n) + ∑ l, b l • vecA B (d.e l) :=
  fun _ _ _ _ _ d _ hn _ hn' => ⟨aCo_mul d hn hn', tCo_mul d hn hn', chr_mul d hn hn', act_fTop d hn⟩

end GlobalTheory.HeisLaw

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.BesselData (hA vecA actV)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_unipotent_action_cocycle : ∀ (D : D7) (L A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : FJDat L A B ι), ∀ n ∈ d.N, ∀ n' ∈ d.N, d.aCo (n * n') = d.aCo n + d.aCo n' ∧ d.tCo (n * n') = d.tCo n + d.tCo n' - hA A (d.aCo n') (d.aCo n) ∧ (∀ ψ : AddChar (AF D.host.F) ℂ, d.chr ψ (n * n') = d.chr ψ n * d.chr ψ n') ∧ ∃ b : Fin d.ρ → AE D, actV B n d.fTop = vecA B d.fTop + ((frameMat B A ι).map (incA D)).mulVec (d.aCo n) + ∑ l, b l • vecA B (d.e l) := by
  first | exact @GlobalTheory.HeisLaw.law | exact GlobalTheory.HeisLaw.law | (intros; apply GlobalTheory.HeisLaw.law <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.BesselData (hA vecA actV)
open scoped TensorProduct

namespace GlobalTheory.Per.ThetaAut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem actHom_tPt {L A : HSp D} (hr : L.rank ≤ A.rank) (c : D.host.E) (γ : GA D A) (a : Fin A.rank → AE D) :
    actHom L A 1 γ (tPt L A c a) = tPt L A c ((Formalism.L2.Theta.mt A γ).mulVec a) := by
  have h1 : cM (1 : Matrix (Fin L.rank) (Fin L.rank) (AE D)) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  unfold actHom
  rw [if_pos hr, BesselCompare.mt_one, h1, Matrix.one_mul]
  ext i k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, tPt, Matrix.of_apply, Matrix.mulVec, dotProduct, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem heis_at_zero (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (u : WA V W) (f : WA V W → ℂ) :
    Heisenberg₂ ψ V W u f 0 = f u := by
  simp only [Heisenberg₂, symplH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]

variable {X : ThetaX D} {T : ThetaTied D X}

theorem exists_heis (Wl : WeilTied D X T) {V W : HSp D} (hne : V.rank ≠ W.rank) (u : WA V W) (Φ : X.Sch V W) :
    ∃ Φ', Wl.evS V W Φ' = Heisenberg₂ Wl.ψ V W u (Wl.evS V W Φ) := by
  have h1 : Wl.evS V W Φ ∈ {f | IsThetaFun Wl.ψ V W f} := by
    rw [← Wl.evS_range V W hne]; exact ⟨Φ, rfl⟩
  have h2 : Heisenberg₂ Wl.ψ V W u (Wl.evS V W Φ) ∈ Set.range (Wl.evS V W) := by
    rw [Wl.evS_range V W hne]; exact GlobalTheory.Mem.ThetaClosed.isThetaFun_heis Wl.ψ_std h1 u
  exact h2

theorem isThetaFun_jacOp (Wl : WeilTied D X T) {L A : HSp D} (hne : L.rank ≠ A.rank) (c : D.host.E)
    (a : Fin A.rank → AE D) (t : AE D) (Φ : X.Sch L A) :
    IsThetaFun Wl.ψ L A (jacOp Wl.ψ L A c a t (Wl.evS L A Φ)) := by
  obtain ⟨Φ', h⟩ := exists_heis Wl hne (tPt L A c a) Φ
  have h2 : jacOp Wl.ψ L A c a t (Wl.evS L A Φ) ∈ Set.range (Wl.evS L A) :=
    ⟨Wl.ψ (cenCo L c t) • Φ', by rw [map_smul, h]; rfl⟩
  rw [Wl.evS_range L A hne] at h2
  exact h2

theorem theta_aut : ∀ (D : D7) (X : ThetaX D) (T : ThetaTied D X) (Wl : WeilTied D X T) (L A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : FJDat L A B ι), 1 < A.rank → ∀ (Φ : X.Sch L A) (g : GA D A), ∀ n ∈ d.N, (∀ γ ∈ d.N, γ ∈ GQ B → d.theta Wl.ψ (omZ Wl L A Φ) (γ * n) g = d.theta Wl.ψ (omZ Wl L A Φ) n g) ∧ ∀ γ ∈ GQ A, ∀ δ, EmbRel B A ι δ γ → d.theta Wl.ψ (omZ Wl L A Φ) (δ * n * δ⁻¹) (γ * g) = d.theta Wl.ψ (omZ Wl L A Φ) n g := by
  intro D X T Wl L A B ι d hA1 Φ g n hn
  have hL : L.rank = 1 := d.line.rank_one
  have hlt : L.rank < A.rank := hL ▸ hA1
  obtain ⟨hrat, -, -, hconj⟩ := GlobalTheory.T.theta_unipotent_conjugation D L A B ι d
  refine ⟨fun γ hγ hq => ?_, fun γ hγ δ hδ => ?_⟩
  · obtain ⟨ha, ht, -⟩ := GlobalTheory.T.theta_unipotent_action_cocycle D L A B ι d γ hγ n hn
    have h1 := ((hrat Wl.ψ Wl.ψ_std.1).1 γ hq).2 _
      (isThetaFun_jacOp Wl hlt.ne d.c (d.aCo n) (d.tCo n) (Wl.om L A X.etaT⁻¹ (X.etaT ^ A.rank) (1, g) Φ))
    unfold FJDat.theta FJDat.jac at *
    rw [ha, ht, ← jacOp_mul Wl.ψ hlt.le]
    exact h1
  · obtain ⟨-, ha, ht, -⟩ := hconj δ γ hδ n hn
    rw [d.theta_eq, d.theta_eq, ha, ht, ← actHom_tPt hlt.le]
    congr 1
    obtain ⟨Φ', h⟩ := exists_heis Wl hlt.ne (tPt L A d.c (d.aCo n)) (Wl.om L A X.etaT⁻¹ (X.etaT ^ A.rank) (1, g) Φ)
    have h1 := Wl.om_heis L A _ _ hlt.ne (resEta_line T hL) (resEta_pow T _) 1 γ _ _ _ h
    have h2 := Wl.om_aut L A _ _ hlt.ne (resEta_line T hL) (resEta_pow T _) 1 (one_mem _) γ hγ Φ'
    rw [h1, h, heis_at_zero, heis_at_zero, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul] at h2
    exact h2

end GlobalTheory.Per.ThetaAut
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.BesselData (hA vecA actV)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_kernel_invariance : ∀ (D : D7) (X : ThetaX D) (T : ThetaTied D X) (Wl : WeilTied D X T) (L A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : FJDat L A B ι), 1 < A.rank → ∀ (Φ : X.Sch L A) (g : GA D A), ∀ n ∈ d.N, (∀ γ ∈ d.N, γ ∈ GQ B → d.theta Wl.ψ (omZ Wl L A Φ) (γ * n) g = d.theta Wl.ψ (omZ Wl L A Φ) n g) ∧ ∀ γ ∈ GQ A, ∀ δ, EmbRel B A ι δ γ → d.theta Wl.ψ (omZ Wl L A Φ) (δ * n * δ⁻¹) (γ * g) = d.theta Wl.ψ (omZ Wl L A Φ) n g := by
  atlas_forward_decl GlobalTheory.Per.ThetaAut.theta_aut
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.BesselData (hA vecA actV)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_continuous : ∀ (D : D7) (X : ThetaX D) (T : ThetaTied D X) (Wl : WeilTied D X T) (V W : HSp D) (χ χ' : X.Chr), V.rank ≠ W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank → ∀ Φ : X.Sch V W, Continuous fun q : (GA D V × GA D W) × WA V W => Wl.evS V W (Wl.om V W χ χ' q.1 Φ) q.2 := by
  first | exact @GlobalTheory.ThetaJointCont.continuous_evS_om | exact GlobalTheory.ThetaJointCont.continuous_evS_om | (intros; apply GlobalTheory.ThetaJointCont.continuous_evS_om <;> assumption)
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.BesselData (hA vecA actV)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Per.FJConv

theorem iterated_integrableOn {G N : Type} [TopologicalSpace G] [FirstCountableTopology G] [MeasurableSpace G]
    [OpensMeasurableSpace G] [TopologicalSpace N] [MeasurableSpace N] [OpensMeasurableSpace N]
    {μ : Measure G} {𝓕 : Set G} {ν : Measure N} {𝓝 : Set N} (hμ : μ 𝓕 ≠ ⊤) (hν : ν 𝓝 ≠ ⊤) {P : G → N → ℂ}
    (hP : Continuous fun q : G × N => P q.1 q.2) {M : ℝ} (hM : ∀ g n, ‖P g n‖ ≤ M) :
    (∀ g, IntegrableOn (P g) 𝓝 ν) ∧ IntegrableOn (fun g => ∫ n in 𝓝, P g n ∂ν) 𝓕 μ := by
  have h1 : ∀ g, Continuous (P g) := fun g => hP.comp (Continuous.prodMk_right g)
  have h2 : ∀ n, Continuous fun g => P g n := fun n => hP.comp (Continuous.prodMk_left n)
  have : IsFiniteMeasure (ν.restrict 𝓝) := isFiniteMeasure_restrict.2 hν
  refine ⟨fun g => Measure.integrableOn_of_bounded (M := M) hν (h1 g).measurable.aestronglyMeasurable
    (.of_forall (hM g)), ?_⟩
  have hc : Continuous fun g => ∫ n in 𝓝, P g n ∂ν :=
    continuous_of_dominated (bound := fun _ => M) (fun g => (h1 g).measurable.aestronglyMeasurable)
      (fun g => .of_forall (hM g)) (integrable_const M) (.of_forall h2)
  exact Measure.integrableOn_of_bounded (M := M * ν.real 𝓝) hμ hc.measurable.aestronglyMeasurable
    (.of_forall fun g => norm_setIntegral_le_of_norm_le_const hν.lt_top fun n _ => hM g n)

theorem continuous_theta {D : D7} {X : ThetaX D} {T : ThetaTied D X} (Wl : WeilTied D X T) {L A B : HSp D}
    {ι : A.V →ₗ[D.host.E] B.V} (d : FJDat L A B ι) (hr : 1 < A.rank) (hψ : Continuous Wl.ψ) (Φ : X.Sch L A) :
    Continuous fun q : GA D A × GA D B => d.theta Wl.ψ (omZ Wl L A Φ) q.2 q.1 := by
  have i0 : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
  have i1 : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  obtain ⟨-, ha, htc, -⟩ := GlobalTheory.T.theta_unipotent_conjugation D L A B ι d
  have hL := d.line.rank_one
  have hθ := GlobalTheory.T.weil_representation_continuous D X T Wl L A X.etaT⁻¹ (X.etaT ^ A.rank) (by omega) (resEta_line T hL) (resEta_pow T _) Φ
  have hcen : Continuous (cenCo L d.c) := continuous_const.mul (ht.comp (continuous_const.mul continuous_id))
  have htp : Continuous (tPt L A d.c) :=
    continuous_pi fun _ => continuous_pi fun k => (continuous_const.mul (continuous_apply k)).neg
  simp only [FJDat.theta_eq]
  exact (hψ.comp (hcen.comp (htc.comp continuous_snd))).mul
    (hθ.comp ((continuous_const.prodMk continuous_fst).prodMk (htp.comp (ha.comp continuous_snd))))

theorem conv_of_isAniso : ∀ (D : D7) (X : ThetaX D) (T : ThetaTied D X) (Wl : WeilTied D X T) (L A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : FJDat L A B ι), 1 < A.rank → IsAniso A → ∀ μ 𝓕, μ.IsHaarMeasure → IsFundamentalDomain (GQ A) 𝓕 μ → ∀ ν 𝓝, IsUnitN B d.eM ν 𝓝 → ∀ s : GA D A → GA D B, (∀ h, EmbRel B A ι (s h) h) → ∀ (Φ : X.Sch L A) φ F, IsAutFun A φ → IsAutFun B F → d.Conv Wl.ψ (omZ Wl L A Φ) μ 𝓕 ν 𝓝 s φ F := by
  intro D X T Wl L A B ι d hr hA μ 𝓕 hμ h𝓕 ν 𝓝 hν s hs Φ φ F hφ hF
  have hψ : IsCharAF D.host.F Wl.ψ := Wl.ψ_std.1
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact D A hA
  obtain ⟨K', hK', hcov'⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B _ _ d.isIsoSub).1
  obtain ⟨s₀, hcont, hrel, hQ⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι d.isom
  obtain rfl : s = s₀ := funext fun h => (hrel h _).1 (hs h)
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have hfin : μ 𝓕 < ⊤ := GlobalTheory.BesselConvDefinite.measure_fundamentalDomain_lt_top (GQ A) hK hcov μ h𝓕
  obtain ⟨hchr, -, -, hconj⟩ := GlobalTheory.T.theta_unipotent_conjugation D L A B ι d
  have haut := GlobalTheory.T.theta_kernel_invariance D X T Wl L A B ι d hr Φ
  have hv : Continuous fun q : GA D A × d.N => (q.2 : GA D B) := continuous_subtype_val.comp continuous_snd
  have hP : Continuous fun q : GA D A × d.N => d.perFun Wl.ψ (omZ Wl L A Φ) s₀ φ F q.1 q.2 :=
    (((hφ.cont.comp continuous_fst).star.mul (hF.cont.comp (hv.mul (hcont.comp continuous_fst)))).mul
      ((continuous_theta Wl d hr hψ.1 Φ).comp (continuous_fst.prodMk hv))).mul ((hchr _ hψ).2.comp hv).star
  obtain ⟨M, hM⟩ := (hK.prod hK').exists_bound_of_continuousOn hP.continuousOn
  refine iterated_integrableOn hfin.ne (by rw [hν.2.2]; exact ENNReal.one_ne_top) hP (M := M) fun g n => ?_
  obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov g
  have hn : s₀ γ⁻¹ * n * (s₀ γ⁻¹)⁻¹ ∈ d.N := (hconj _ _ ((hrel _ _).2 rfl) n n.2).1
  obtain ⟨γ', hγ', k', hk', e⟩ := hcov' ⟨_, hn⟩
  have e' : s₀ γ⁻¹ * n * (s₀ γ⁻¹)⁻¹ = (γ' : GA D B) * k' := congrArg Subtype.val e
  have e1 : (n : GA D B) = s₀ γ * (γ' * k') * (s₀ γ)⁻¹ := by
    rw [← e']; simp only [map_inv, inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  have e2 : (n : GA D B) * s₀ (γ * k) = s₀ γ * (γ' * (k' * s₀ k)) := by
    rw [e1]; simp only [map_mul, mul_assoc, inv_mul_cancel_left]
  have e3 : d.theta Wl.ψ (omZ Wl L A Φ) n (γ * k) = d.theta Wl.ψ (omZ Wl L A Φ) k' k := by
    rw [e1, (haut k _ (mul_mem γ'.2 k'.2)).2 γ hγ _ ((hrel _ _).2 rfl), (haut k _ k'.2).1 _ γ'.2 hγ']
  have hc : ∀ x, ‖d.chr Wl.ψ x‖ = 1 := fun x => hψ.2.1 _
  refine le_trans (le_of_eq ?_) (hM (k, k') ⟨hk, hk'⟩)
  simp only [FJDat.perFun, norm_mul, norm_star, hc]
  rw [e2, e3, hφ.left γ hγ, hF.left _ (hQ γ hγ), hF.left (γ' : GA D B) hγ']

end GlobalTheory.Per.FJConv
end
