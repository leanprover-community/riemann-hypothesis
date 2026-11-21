import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrLink
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnWittFrameBasisBlockGramStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralFiniteAdeleIsoCommutesWithConjugation
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MulVecMemLatS
import BuildAid.ForwardExisting

section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralFiniteAdeleIso_commutes_with_conjugation : ∀ (D : D7) (X : HidaSetting D) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), IsAdeleIso X ιA → ∀ a, ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (ιA a) := by
  first | exact @GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA | exact GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA | (intros; apply GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA <;> assumption)
end

section
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace GlobalTheory.St.G

theorem latTransport : ∀ (D : D7) (X : HidaSetting D) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), IsAdeleIso X ιA → ∀ w : Fin X.B.I.n → D.host.E ⊗[D.host.F] Ad D.host.F, w ∈ hat D.host.F ((VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E))) ↔ (fun i => ιA.symm (w i)) ∈ X.B.I.Lf := by
  intro D X ιA hA w
  obtain ⟨h1, h2⟩ := hA
  have hgen : ∀ x : X.B.I.E, ιA.symm (Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) (X.ιE x)) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) x := by
    intro x; rw [RingEquiv.symm_apply_eq]; exact (h1 x).symm
  have hgen' : ∀ x : X.B.I.E, ιA (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) x) =
      Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) (X.ιE x) := h1
  have hint : ∀ a, a ∈ IntAf X.B.I.F X.B.I.E ↔ ιA a ∈ OAd D.host.F D.host.E := h2
  have hL' : ∀ c : Fin X.B.I.n → D.host.E,
      c ∈ (VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E)) ↔
        (fun i => X.ιE.symm (c i)) ∈ X.B.I.L := by
    intro c
    rw [X.L_eq, Submodule.mem_comap]
    simp [Fintype.linearCombination_apply]
  constructor
  · intro hw
    change w ∈ Submodule.span _ _ at hw
    change (fun i => ιA.symm (w i)) ∈ Submodule.span _ _
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      refine Submodule.subset_span ⟨⟨fun i => X.ιE.symm (c i), (hL' c).1 hc⟩, ?_⟩
      funext i
      simp only
      rw [← hgen, RingEquiv.apply_symm_apply]
    | zero =>
      convert Submodule.zero_mem _ using 1
      funext i; simp
    | add x y _ _ hx hy =>
      have : (fun i => ιA.symm ((x + y) i)) = (fun i => ιA.symm (x i)) + (fun i => ιA.symm (y i)) := by
        funext i; simp
      rw [this]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      have hr : ιA.symm (r : D.host.E ⊗[D.host.F] Ad D.host.F) ∈ IntAf X.B.I.F X.B.I.E := by
        rw [hint, RingEquiv.apply_symm_apply]; exact r.2
      have : (fun i => ιA.symm ((r • x) i)) = (⟨_, hr⟩ : IntAf X.B.I.F X.B.I.E) • (fun i => ιA.symm (x i)) := by
        funext i; simp [Subring.smul_def, smul_eq_mul, map_mul]
      rw [this]; exact Submodule.smul_mem _ _ hx
  · intro hw
    change _ ∈ Submodule.span _ _ at hw
    change w ∈ Submodule.span _ _
    have key : ∀ v, v ∈ Submodule.span (IntAf X.B.I.F X.B.I.E)
        (Set.range fun x : X.B.I.L => fun i => Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((x : Fin X.B.I.n → X.B.I.E) i)) →
        (fun i => ιA (v i)) ∈ hat D.host.F ((VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E))) := by
      intro v hv
      change _ ∈ Submodule.span _ _
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨x, rfl⟩ := hx
        refine Submodule.subset_span ⟨fun i => X.ιE ((x : Fin X.B.I.n → X.B.I.E) i), (hL' _).2 ?_, ?_⟩
        · simpa using x.2
        · funext i; simp only; rw [hgen']
      | zero =>
      convert Submodule.zero_mem _ using 1
      funext i; simp
      | add x y _ _ hx hy =>
        have : (fun i => ιA ((x + y) i)) = (fun i => ιA (x i)) + (fun i => ιA (y i)) := by
          funext i; simp
        rw [this]; exact Submodule.add_mem _ hx hy
      | smul r x _ hx =>
        have hr : ιA (r : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ OAd D.host.F D.host.E := (hint _).1 r.2
        have : (fun i => ιA ((r • x) i)) = (⟨_, hr⟩ : OAd D.host.F D.host.E) • (fun i => ιA (x i)) := by
          funext i; simp [Subring.smul_def, smul_eq_mul, map_mul]
        rw [this]; exact Submodule.smul_mem _ _ hx
    have := key _ hw
    have e : (fun i => ιA (ιA.symm (w i))) = w := funext fun i => by simp
    rw [e] at this
    exact this

end GlobalTheory.St.G
end

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLattice_concreteData_eq_adelicSpan : ∀ (D : D7) (X : HidaSetting D) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), IsAdeleIso X ιA → ∀ w : Fin X.B.I.n → D.host.E ⊗[D.host.F] Ad D.host.F, w ∈ hat D.host.F ((VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E))) ↔ (fun i => ιA.symm (w i)) ∈ X.B.I.Lf := by
  atlas_forward_decl GlobalTheory.St.G.latTransport
end

section
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G

theorem coordLat_isLat (D : D7) (X : HidaSetting D) :
    IsLat ((VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E))) := by
  have hcomb : ∀ x : Fin _ → D.host.E,
      Fintype.linearCombination D.host.E X.bas x = X.bas.equivFun.symm x := by
    intro x
    rw [Fintype.linearCombination_apply, Module.Basis.equivFun_symm_apply]
  have heq : (VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E)) =
      (VS D).L0.map (X.bas.equivFun.restrictScalars (𝓞 D.host.E)).toLinearMap := by
    ext x
    simp only [Submodule.mem_comap, LinearMap.restrictScalars_apply, hcomb, Submodule.mem_map,
      LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply]
    constructor
    · intro hx
      exact ⟨_, hx, X.bas.equivFun.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [heq]
  refine ⟨Module.Finite.iff_fg.2 ((VS D).standardTuple_isLattice.fg.map _), ?_⟩
  have : ((VS D).L0.map (X.bas.equivFun.restrictScalars (𝓞 D.host.E)).toLinearMap : Set (Fin _ → D.host.E)) =
      X.bas.equivFun.toLinearMap '' ((VS D).L0 : Set (VS D).V) := rfl
  rw [this, ← Submodule.map_span, (VS D).standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]

end GlobalTheory.St.G
end

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordinateLattice_selfDual_isFullRank : ∀ (D : D7) (X : HidaSetting D), IsLat ((VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E))) := by
  atlas_forward_decl GlobalTheory.St.G.coordLat_isLat
end

section
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.St.G.MHat

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

variable {D : D7}

theorem sum_swap4 {α β γ δ R : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [AddCommMonoid R]
    (f : α → β → γ → δ → R) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ d, ∑ b, f a b c d := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun c _ => ?_
        exact Finset.sum_comm

theorem sigR_inclE (I : Formalism.MainNotions.S.AutInst) (e : I.E) :
    Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) e) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (star e) := by
  simp only [Formalism.UG.sigR, Formalism.UG.inclE, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem hA_sum (I : Formalism.MainNotions.S.AutInst) {ι κ : Type} [Fintype ι] [Fintype κ]
    (c : ι → I.E ⊗[I.F] Af I.F) (v : ι → Fin I.n → I.E) (d : κ → I.E ⊗[I.F] Af I.F)
    (w : κ → Fin I.n → I.E) :
    hA I (∑ i, c i • incl I (v i)) (∑ j, d j • incl I (w j)) =
      ∑ i, ∑ j, sigA I (c i) *
        Formalism.UG.inclE (F := I.F) (Af I.F) (Formalism.UG.hform (starRingEnd I.E) I.J (v i) (w j)) * d j := by
  simp only [hA, Formalism.UG.hform, incl, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
    Matrix.map_apply, sigR_inclE, Finset.sum_mul, Finset.mul_sum, starRingEnd_apply]
  rw [sum_swap4, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_; intro i _
  refine Finset.sum_congr rfl ?_; intro j _
  refine Finset.sum_congr rfl ?_; intro k _
  refine Finset.sum_congr rfl ?_; intro l _
  ring

theorem hform_cols (I : Formalism.MainNotions.S.AutInst) {ι : Type} [Fintype ι] (Q : Matrix (Fin I.n) ι I.E) (a b : ι) :
    Formalism.UG.hform (starRingEnd I.E) I.J (fun k => Q k a) (fun l => Q l b) =
      ((Q.map (starRingEnd I.E))ᵀ * I.J * Q) a b := by
  simp only [Formalism.UG.hform, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem frame_indep (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hW : WittX X u wt) {R : Type} [CommRing R] (φ : X.B.I.E →+* R) (c : Fin (D.R.N 0) → R)
    (h : ∀ i, ∑ j, c j * φ (X.crd (qFr wt j) i) = 0) : c = 0 := by
  obtain ⟨Q, Qi, G', -, hQiQ, hq, -, -, -, -, -⟩ := GlobalTheory.T.columnWittFrame_basis_blockGram D X u wt hW
  let v : (Fin (D.R.N 0) ⊕ (Fin D.R.rS ⊕ Fin D.R.rS ⊕ Unit)) → R := Sum.elim c 0
  have h0 : (Q.map φ) *ᵥ v = 0 := by
    funext i
    simp only [v, Matrix.mulVec, dotProduct, Matrix.map_apply, Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
    rw [← h i]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [hq, mul_comm]
  have h1 : v = 0 := by
    have hone : (Qi.map φ * Q.map φ) *ᵥ v = v := by
      rw [← Matrix.map_mul, hQiQ, Matrix.map_one φ (map_zero φ) (map_one φ), Matrix.one_mulVec]
    rw [← hone, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
  funext j
  have := congrFun h1 (Sum.inl j)
  simpa [v] using this

theorem symm_inclE (X : HidaSetting D)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) (hι : IsAdeleIso X ιA)
    (c : D.host.E) :
    ιA.symm (Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) c) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm c) := by
  rw [RingEquiv.symm_apply_eq, hι.1, RingEquiv.apply_symm_apply]

theorem embA_apply (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F)
    (x : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) (i : Fin X.B.I.n) :
    embA X wt ιA x i = ∑ j, ιA.symm (x j) * Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.crd (qFr wt j) i) := by
  simp [embA, qA, incl]

theorem embA_injective (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hW : WittX X u wt) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) :
    Function.Injective (embA X wt ιA) := by
  intro a b hab
  have h := frame_indep X u wt hW (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F))
    (fun j => ιA.symm (a j - b j)) (fun i => by
      have := congrFun hab i
      rw [embA_apply, embA_apply] at this
      simp only [map_sub, sub_mul, Finset.sum_sub_distrib, this, sub_self])
  funext j
  have := congrFun h j
  simpa [sub_eq_zero] using this

theorem hform_qFr (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hW : WittX X u wt) (i j : Fin (D.R.N 0)) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.crd (qFr wt i)) (X.crd (qFr wt j)) =
      X.ιE.symm (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _) i j) := by
  obtain ⟨Q, Qi, G', -, -, hq, -, -, -, -, hG⟩ := GlobalTheory.T.columnWittFrame_basis_blockGram D X u wt hW
  have hc : ∀ j, X.crd (qFr wt j) = fun k => Q k (Sum.inl j) := fun j => funext fun k => (hq j k).symm
  rw [hc, hc, hform_cols, hG, Matrix.fromBlocks_apply₁₁, Matrix.map_apply]

theorem hA_embA (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hW : WittX X u wt) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F)
    (hι : IsAdeleIso X ιA) (x y : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) :
    ιA (hA X.B.I (embA X wt ιA x) (embA X wt ιA y)) =
      hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F) x y := by
  unfold embA qA
  rw [hA_sum]
  simp only [hform_qFr X u wt hW, map_sum, map_mul, GlobalTheory.T.integralFiniteAdeleIso_commutes_with_conjugation D X ιA hι, RingEquiv.apply_symm_apply,
    hι.1]
  simp only [hR, Formalism.UG.hform, Matrix.map_apply]

theorem hA_incl_embA (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) (v : Fin X.B.I.n → X.B.I.E)
    (x : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) :
    hA X.B.I (incl X.B.I v) (embA X wt ιA x) =
      ∑ j, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)
        (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J v (X.crd (qFr wt j))) * ιA.symm (x j) := by
  have h1 : incl X.B.I v = ∑ _i : Unit, (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • incl X.B.I v := by simp
  rw [h1]
  unfold embA qA
  rw [hA_sum]
  simp

theorem hform_orth (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hW : WittX X u wt) (j : Fin (D.R.N 0)) :
    (∀ a, Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.eR a) (X.crd (qFr wt j)) = 0) ∧
    (∀ a, Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.fR a) (X.crd (qFr wt j)) = 0) ∧
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.zR u) (X.crd (qFr wt j)) = 0 := by
  obtain ⟨Q, Qi, G', -, -, hq, he, hf, hz, -, hG⟩ := GlobalTheory.T.columnWittFrame_basis_blockGram D X u wt hW
  have hc : X.crd (qFr wt j) = fun k => Q k (Sum.inl j) := funext fun k => (hq j k).symm
  refine ⟨fun a => ?_, fun a => ?_, ?_⟩
  · have : X.eR a = fun k => Q k (Sum.inr (Sum.inl a)) := funext fun k => (he a k).symm
    rw [hc, this, hform_cols, hG, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
  · have : X.fR a = fun k => Q k (Sum.inr (Sum.inr (Sum.inl a))) := funext fun k => (hf a k).symm
    rw [hc, this, hform_cols, hG, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
  · have : X.zR u = fun k => Q k (Sum.inr (Sum.inr (Sum.inr ()))) := funext fun k => (hz k).symm
    rw [hc, this, hform_cols, hG, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]

theorem fmat_embA (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F) (h : Hfin X u)
    (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F))
    (hR : RepF X wt ιA (h : X.B.I.Gf) y) (x : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) :
    X.B.I.fmat (h : X.B.I.Gf) *ᵥ embA X wt ιA x = embA X wt ιA (y.1.1 *ᵥ x) := by
  unfold embA
  rw [Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul]
  unfold RepF at hR
  simp only [hR, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  rw [Matrix.mulVec, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, mul_comm]

theorem mem_hat_Mq (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hW : WittX X u wt) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F)
    (hι : IsAdeleIso X ιA) (x : Fin (D.R.N 0) → D.host.E ⊗[D.host.F] Ad D.host.F) :
    x ∈ hat D.host.F (Mq wt) ↔ embA X wt ιA x ∈ X.B.I.Lf := by
  let Q' : Matrix (Fin X.B.I.n) (Fin (D.R.N 0)) D.host.E := Matrix.of fun i j => X.bas.repr (qFr wt j) i
  have hM : Mq wt = ((VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E))).comap (Q'.mulVecLin.restrictScalars (𝓞 D.host.E)) := by
    ext c
    simp only [Mq, Submodule.mem_comap, LinearMap.restrictScalars_apply, Fintype.linearCombination_apply,
      Matrix.mulVecLin_apply]
    have hv : ∑ i, (Q' *ᵥ c) i • X.bas i = ∑ j, c j • qFr wt j := by
      calc ∑ i, (Q' *ᵥ c) i • X.bas i = ∑ i, ∑ j, c j • (X.bas.repr (qFr wt j) i • X.bas i) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [Q', Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_smul, smul_smul]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [mul_comm]
        _ = ∑ j, c j • ∑ i, X.bas.repr (qFr wt j) i • X.bas i := by
            rw [Finset.sum_comm]
            simp only [Finset.smul_sum]
        _ = ∑ j, c j • qFr wt j := by simp only [X.bas.sum_repr]
    rw [hv]
  have hinj : Function.Injective Q'.mulVec := by
    intro a b hab
    have h0 : Q' *ᵥ (a - b) = 0 := by rw [Matrix.mulVec_sub, hab, sub_self]
    have h := frame_indep X u wt hW (RingHom.id X.B.I.E) (fun j => X.ιE.symm ((a - b) j)) (fun i => by
      have h1 := congrFun h0 i
      simp only [Q', Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at h1
      have h2 : ∑ j, X.ιE.symm ((a - b) j) * (RingHom.id X.B.I.E) (X.crd (qFr wt j) i) =
          X.ιE.symm (∑ j, X.bas.repr (qFr wt j) i * (a - b) j) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, mul_comm]
        rfl
      rw [h2, h1, map_zero])
    funext j
    have := congrFun h j
    simpa [sub_eq_zero] using this
  rw [hM, (GlobalTheory.St.G.Inter.hat_comap _ _ _ _ Q' hinj _ (GlobalTheory.T.coordinateLattice_selfDual_isFullRank D X)).2 x, GlobalTheory.T.adelicLattice_concreteData_eq_adelicSpan D X ιA hι]
  have he : (fun i => ιA.symm ((Q'.map (Formalism.UG.inclE (F := D.host.F) (Ad D.host.F)) *ᵥ x) i)) = embA X wt ιA x := by
    funext i
    rw [embA_apply]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, symm_inclE X ιA hι, Q',
      Matrix.of_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    rfl
  rw [he]

theorem mhat_coords : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → (∀ x, x ∈ hat D.host.F (Mq wt) ↔ embA X wt ιA x ∈ X.B.I.Lf) ∧ (∀ x y, ιA (hA X.B.I (embA X wt ιA x) (embA X wt ιA y)) = hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F) x y) ∧ Function.Injective (embA X wt ιA) ∧ (∀ x a, hA X.B.I (incl X.B.I (X.eR a)) (embA X wt ιA x) = 0 ∧ hA X.B.I (incl X.B.I (X.fR a)) (embA X wt ιA x) = 0) ∧ (∀ x, hA X.B.I (incl X.B.I (X.zR u)) (embA X wt ιA x) = 0) ∧ ∀ (h : Hfin X u) (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)), RepF X wt ιA (h : X.B.I.Gf) y → ∀ x, X.B.I.fmat (h : X.B.I.Gf) *ᵥ embA X wt ιA x = embA X wt ιA (y.1.1 *ᵥ x) := by
  intro D X u wt ιA hW hι
  refine ⟨mem_hat_Mq X u wt hW ιA hι, hA_embA X u wt hW ιA hι, embA_injective X u wt hW ιA, fun x a => ?_,
    fun x => ?_, fun h y hR x => fmat_embA X u wt ιA h y hR x⟩
  · rw [hA_incl_embA, hA_incl_embA]
    constructor
    · simp [(hform_orth X u wt hW _).1 a]
    · simp [(hform_orth X u wt hW _).2.1 a]
  · rw [hA_incl_embA]
    simp [(hform_orth X u wt hW _).2.2]

end GlobalTheory.St.G.MHat

end
end

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicColumnLattice_eq_spanPart_transportedFrame : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), WittX X u wt → IsAdeleIso X ιA → (∀ x, x ∈ hat D.host.F (Mq wt) ↔ embA X wt ιA x ∈ X.B.I.Lf) ∧ (∀ x y, ιA (hA X.B.I (embA X wt ιA x) (embA X wt ιA y)) = hR (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F) x y) ∧ Function.Injective (embA X wt ιA) ∧ (∀ x a, hA X.B.I (incl X.B.I (X.eR a)) (embA X wt ιA x) = 0 ∧ hA X.B.I (incl X.B.I (X.fR a)) (embA X wt ιA x) = 0) ∧ (∀ x, hA X.B.I (incl X.B.I (X.zR u)) (embA X wt ιA x) = 0) ∧ ∀ (h : Hfin X u) (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _)) (Ad D.host.F)), RepF X wt ιA (h : X.B.I.Gf) y → ∀ x, X.B.I.fmat (h : X.B.I.Gf) *ᵥ embA X wt ιA x = embA X wt ιA (y.1.1 *ᵥ x) := by
  atlas_forward_decl GlobalTheory.St.G.MHat.mhat_coords
end
