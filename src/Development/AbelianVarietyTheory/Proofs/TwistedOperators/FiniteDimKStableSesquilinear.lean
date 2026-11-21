import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStableOfIsGKSub
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CenterActionSmoothCommuting
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmOfMemGkGen
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GelfandTransposeEqOfInvariantWords

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.KTypeRep

open GlobalTheory.KTypeProj GlobalTheory.Published.AutFin

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

theorem conj_UH (τ : D.what₂.Tau) (k : Formalism.REAL.KG (M.ε τ)) :
    (M.fr τ)⁻¹ * Formalism.REAL.toMK k * M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
  GlobalTheory.Published.AutFin.conj_mem_UH (M.fr_unit τ) (M.fr_gram τ) k

theorem fr_mul_inv (τ : D.what₂.Tau) : M.fr τ * (M.fr τ)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ))

theorem fr_inv_mul (τ : D.what₂.Tau) : (M.fr τ)⁻¹ * M.fr τ = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ))

theorem conj_inK (τ : D.what₂.Tau) (k : Formalism.REAL.KG (M.ε τ)) :
    GlobalTheory.CuspGK.InK M τ ((M.fr τ)⁻¹ * Formalism.REAL.toMK k * M.fr τ) := by
  refine ⟨conj_UH M τ k, ?_⟩
  have hc : M.fr τ * ((M.fr τ)⁻¹ * Formalism.REAL.toMK k * M.fr τ) * (M.fr τ)⁻¹ =
      (M.fr τ * (M.fr τ)⁻¹) * Formalism.REAL.toMK k * (M.fr τ * (M.fr τ)⁻¹) := by
    simp only [mul_assoc]
  rw [hc, fr_mul_inv M τ, one_mul, mul_one]
  exact k.2

theorem kAt_one (hθ : IsInfFam (D := D) θ) (τ : D.what₂.Tau) : kAt θ V τ (M.ε τ) (M.fr τ) 1 = 1 := by
  show atTau θ V τ ((M.fr τ)⁻¹ * Formalism.REAL.toMK (1 : Formalism.REAL.KG (M.ε τ)) * M.fr τ) = 1
  have h1 : Formalism.REAL.toMK (1 : Formalism.REAL.KG (M.ε τ)) = 1 := rfl
  rw [h1, mul_one, fr_inv_mul M τ]
  exact GlobalTheory.PointAtPlaceHom.atTau_one hθ V τ

theorem kAt_mul (hθ : IsInfFam (D := D) θ) (τ : D.what₂.Tau) (a b : Formalism.REAL.KG (M.ε τ)) :
    kAt θ V τ (M.ε τ) (M.fr τ) (a * b) = kAt θ V τ (M.ε τ) (M.fr τ) a * kAt θ V τ (M.ε τ) (M.fr τ) b := by
  show atTau θ V τ ((M.fr τ)⁻¹ * Formalism.REAL.toMK (a * b) * M.fr τ) =
    atTau θ V τ ((M.fr τ)⁻¹ * Formalism.REAL.toMK a * M.fr τ) * atTau θ V τ ((M.fr τ)⁻¹ * Formalism.REAL.toMK b * M.fr τ)
  rw [← GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ (conj_UH M τ a) (conj_UH M τ b)]
  have hab : Formalism.REAL.toMK (a * b) = Formalism.REAL.toMK a * Formalism.REAL.toMK b := rfl
  have hsplit : (M.fr τ)⁻¹ * Formalism.REAL.toMK a * M.fr τ * ((M.fr τ)⁻¹ * Formalism.REAL.toMK b * M.fr τ) =
      (M.fr τ)⁻¹ * Formalism.REAL.toMK a * (M.fr τ * (M.fr τ)⁻¹) * Formalism.REAL.toMK b * M.fr τ := by
    simp only [mul_assoc]
  rw [hsplit, fr_mul_inv M τ, mul_one, hab]
  simp only [mul_assoc]

theorem continuous_kAt (hθ : IsInfFam (D := D) θ) (τ : D.what₂.Tau) :
    Continuous fun k => kAt θ V τ (M.ε τ) (M.fr τ) k := by
  have hK : Continuous fun k : Formalism.REAL.KG (M.ε τ) => Formalism.REAL.toMK k :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hconj : Continuous fun k : Formalism.REAL.KG (M.ε τ) => (M.fr τ)⁻¹ * Formalism.REAL.toMK k * M.fr τ :=
    (continuous_const.matrix_mul hK).matrix_mul continuous_const
  exact (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ).comp_continuous hconj fun k => conj_UH M τ k

def kRep (hθ : IsInfFam (D := D) θ) (Y : Submodule ℂ (GA D V → ℂ)) (hY : KStable θ M Y) (τ : D.what₂.Tau) :
    Representation ℂ (Formalism.REAL.KG (M.ε τ)) Y where
  toFun k := (rTrL (kAt θ V τ (M.ε τ) (M.fr τ) k)).restrict fun f hf => hY τ _ (conj_inK M τ k) f hf
  map_one' := by
    refine LinearMap.ext fun w => Subtype.ext (funext fun x => ?_)
    show w.1 (x * kAt θ V τ (M.ε τ) (M.fr τ) 1) = w.1 x
    rw [kAt_one M hθ, mul_one]
  map_mul' a b := by
    refine LinearMap.ext fun w => Subtype.ext (funext fun x => ?_)
    show w.1 (x * kAt θ V τ (M.ε τ) (M.fr τ) (a * b)) =
      w.1 (x * kAt θ V τ (M.ε τ) (M.fr τ) a * kAt θ V τ (M.ε τ) (M.fr τ) b)
    rw [kAt_mul M hθ, mul_assoc]

theorem isContRep_kRep (hθ : IsInfFam (D := D) θ) (Y : Submodule ℂ (GA D V → ℂ)) [FiniteDimensional ℂ Y]
    (hY : KStable θ M Y) (hc : ∀ f ∈ Y, Continuous f) (τ : D.what₂.Tau) : IsContRep (kRep M hθ Y hY τ) := by
  intro ℓ w
  have hℓ : Continuous ℓ := LinearMap.continuous_of_finiteDimensional ℓ
  refine hℓ.comp (continuous_induced_rng.2 (continuous_pi fun x => ?_))
  show Continuous fun k => (w : GA D V → ℂ) (x * kAt θ V τ (M.ε τ) (M.fr τ) k)
  exact (hc _ w.2).comp (continuous_const.mul (continuous_kAt M hθ τ))

end GlobalTheory.KTypeRep

theorem GlobalTheory.KTypeRep.exists_contRep_types : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ Y : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ Y → GlobalTheory.KTypeProj.KStable θ M Y → (∀ f ∈ Y, Continuous f) →
    ∀ τ, ∃ ρ : Representation ℂ (Formalism.REAL.KG (M.ε τ)) Y, GlobalTheory.Published.AutFin.IsContRep ρ ∧
      ∀ T : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ),
        (∀ i, ∀ w ∈ Y, T (GlobalTheory.KTypeProj.rhoK θ M i w) = GlobalTheory.KTypeProj.rhoK θ M i (T w)) →
        ∀ w : Y, GlobalTheory.Published.AutFin.HasTypeAt θ V τ (M.ε τ) (M.fr τ) ρ (T w) := by
  intro D θ V S M hθ Y hfin hY hc τ
  haveI := hfin
  refine ⟨GlobalTheory.KTypeRep.kRep M hθ Y hY τ, GlobalTheory.KTypeRep.isContRep_kRep M hθ Y hY hc τ, ?_⟩
  intro T hT w
  refine GlobalTheory.Published.AutFin.hasTypeAt_of_map θ V τ (M.ε τ) (M.fr τ) _ (T ∘ₗ Y.subtype) (fun k u => ?_) w
  exact hT ⟨(τ, (M.fr τ)⁻¹ * Formalism.REAL.toMK k * M.fr τ), GlobalTheory.KTypeRep.conj_inK M τ k⟩ u.1 u.2

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuousRep_rightTranslation_maxCompactStable : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ Y : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ Y → GlobalTheory.KTypeProj.KStable θ M Y → (∀ f ∈ Y, Continuous f) →
    ∀ τ, ∃ ρ : Representation ℂ (Formalism.REAL.KG (M.ε τ)) Y, GlobalTheory.Published.AutFin.IsContRep ρ ∧
      ∀ T : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ),
        (∀ i, ∀ w ∈ Y, T (GlobalTheory.KTypeProj.rhoK θ M i w) = GlobalTheory.KTypeProj.rhoK θ M i (T w)) →
        ∀ w : Y, GlobalTheory.Published.AutFin.HasTypeAt θ V τ (M.ε τ) (M.fr τ) ρ (T w) := by
  atlas_forward_decl GlobalTheory.KTypeRep.exists_contRep_types
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

namespace GlobalTheory.RderCAdjoint

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

theorem Rder_neg_dir (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    Rder θ V τ (-X) φ = -Rder θ V τ X φ := by
  funext g
  have := deriv_comp_neg (fun t : ℝ => φ (g * oneP θ V τ X t)) 0
  simpa only [Rder, oneP, smul_neg, neg_smul, neg_zero, Pi.neg_apply] using this

theorem conjAt_adjoint (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    conjAt V τ ((gramAt D V τ)⁻¹ * Zᴴ * gramAt D V τ) = -Z := by
  have hu := GlobalTheory.SmoothAutCheck.gramAt_unit V τ
  have hH := GlobalTheory.SmoothAutCheck.gramAt_herm V τ
  unfold conjAt
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hH,
    ← mul_assoc, nonsing_inv_mul _ hu, one_mul, mul_assoc, nonsing_inv_mul _ hu, mul_one]

theorem RderC_adjoint_eq (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    RderC θ V τ ((gramAt D V τ)⁻¹ * Zᴴ * gramAt D V τ) φ =
      -Rder θ V τ ((1 / 2 : ℂ) • (Z + conjAt V τ Z)) φ +
        Complex.I • Rder θ V τ ((1 / (2 * Complex.I)) • (Z - conjAt V τ Z)) φ := by
  unfold RderC
  rw [conjAt_adjoint]
  have hW : (gramAt D V τ)⁻¹ * Zᴴ * gramAt D V τ = -conjAt V τ Z := by simp [conjAt]
  rw [hW, ← Rder_neg_dir, ← smul_neg, neg_add, add_comm (-Z), neg_sub_neg]

theorem rderC_adjoint : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau)
    (A : Submodule ℂ (GA D V → ℂ)) (b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ),
    (∀ X ∈ lieAt V τ, ∀ x ∈ A, ∀ y ∈ A, b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) →
    ∀ (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ), ∀ x ∈ A, ∀ y ∈ A,
      b x (RderC θ V τ Z y) = b (RderC θ V τ ((gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ) x) y := by
  intro D θ V τ A b hb Z x hx y hy
  obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  rw [RderC_adjoint_eq]
  unfold RderC
  rw [map_add, map_smul, hb _ h1 x hx y hy, hb _ h2 x hx y hy, map_add, map_neg, map_smulₛₗ]
  simp

end GlobalTheory.RderCAdjoint

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexDerivative_adjoint_of_skew_form : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau)
    (A : Submodule ℂ (GA D V → ℂ)) (b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ),
    (∀ X ∈ lieAt V τ, ∀ x ∈ A, ∀ y ∈ A, b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) →
    ∀ (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ), ∀ x ∈ A, ∀ y ∈ A,
      b x (RderC θ V τ Z y) = b (RderC θ V τ ((gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ) x) y := by
  atlas_forward_decl GlobalTheory.RderCAdjoint.rderC_adjoint
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
open scoped Matrix

noncomputable section

namespace GlobalTheory.GelfSymm

open scoped Matrix

open GlobalTheory.Mem.RealTranslate (derEnd)
open GlobalTheory.RegSch (wordDer)

theorem prod_map_neg {R : Type} [Ring R] [Algebra ℂ R] :
    ∀ l : List R, (l.map fun a => -a).prod = (-1 : ℂ) ^ l.length • l.prod
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.prod_cons, prod_map_neg l, List.prod_cons, List.length_cons, pow_succ,
      mul_smul_comm, neg_mul, mul_comm, mul_smul, neg_one_smul, smul_neg]

theorem sum_words_rev {R : Type} [Ring R] [Algebra ℂ R] {n : ℕ} (φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] R)
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : IsUnit M.det) (k : ℕ) :
    ∑ idx : Fin (k + 1) → Fin n,
      (List.ofFn fun a : Fin (k + 1) => φ (-(M * (Matrix.single (idx a) (idx (a + 1)) 1)ᵀ * M⁻¹))).reverse.prod =
    (-1 : ℂ) ^ (k + 1) • ∑ idx : Fin (k + 1) → Fin n,
      (List.ofFn fun a : Fin (k + 1) => φ (Matrix.single (idx a) (idx (a + 1)) 1)).prod := by
  let ψ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Rᵐᵒᵖ := (MulOpposite.opLinearEquiv ℂ).toLinearMap ∘ₗ φ
  have h := congrArg MulOpposite.unop (GlobalTheory.RegSch.GelfCyc.sum_words ψ M hM k)
  have e : ∀ l : List R, (l.map MulOpposite.op).prod = MulOpposite.op l.reverse.prod := fun l => by
    rw [MulOpposite.op_list_prod, List.map_reverse, List.reverse_reverse]
  have e' : ∀ l : List R, (l.map MulOpposite.op).reverse.prod = MulOpposite.op l.prod := fun l =>
    (MulOpposite.op_list_prod l).symm
  have hψ : ∀ g : Fin (k + 1) → Matrix (Fin n) (Fin n) ℂ, (List.ofFn fun a => ψ (g a)) = (List.ofFn fun a => φ (g a)).map MulOpposite.op := by
    intro g; rw [List.map_ofFn]; rfl
  have hs : ∀ f : (Fin (k + 1) → Fin n) → R, ∑ i, MulOpposite.op (f i) = MulOpposite.op (∑ i, f i) :=
    fun f => (map_sum MulOpposite.opAddEquiv f _).symm
  simp only [hψ, e, e', hs, MulOpposite.unop_smul, MulOpposite.unop_op] at h
  exact h

end GlobalTheory.GelfSymm

namespace GlobalTheory.GelfSymm

open scoped Matrix
open GlobalTheory.Mem.RealTranslate (derEnd)
open GlobalTheory.RegSch (wordDer)

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem wordDer_append (τ : D.what₂.Tau) (l l' : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)) (f : GA D V → ℂ) :
    wordDer θ V τ (l ++ l') f = wordDer θ V τ l (wordDer θ V τ l' f) := by
  simp only [wordDer, List.foldr_append]

theorem wordDer_mem {τ : D.what₂.Tau} {A : Submodule ℂ (GA D V → ℂ)} (hA : ∀ Z, ∀ f ∈ A, RderC θ V τ Z f ∈ A)
    (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)) {f : GA D V → ℂ} (hf : f ∈ A) : wordDer θ V τ l f ∈ A := by
  induction l with
  | nil => exact hf
  | cons Z l ih => exact hA Z _ ih

theorem adj_word {τ : D.what₂.Tau} {A : Submodule ℂ (GA D V → ℂ)} (hA : ∀ Z, ∀ f ∈ A, RderC θ V τ Z f ∈ A)
    (b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ)
    (hb : ∀ Z, ∀ x ∈ A, ∀ y ∈ A, b x (RderC θ V τ Z y) =
      b (RderC θ V τ ((gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ) x) y) :
    ∀ (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)), ∀ x ∈ A, ∀ y ∈ A,
      b x (wordDer θ V τ l y) =
        b (wordDer θ V τ (l.reverse.map fun Z => (gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ) x) y
  | [], x, _, y, _ => rfl
  | Z :: l, x, hx, y, hy => by
    show b x (RderC θ V τ Z (wordDer θ V τ l y)) = _
    rw [hb Z x hx _ (wordDer_mem hA l hy), adj_word hA b hb l _ (hA _ _ hx) y hy, List.reverse_cons, List.map_append,
      wordDer_append]
    rfl

end GlobalTheory.GelfSymm

open GlobalTheory.Mem.RealTranslate (derEnd) in
open GlobalTheory.RegSch (wordDer) in
open GlobalTheory.GelfSymm in

theorem GlobalTheory.GelfSymm.gelf_symm : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), IsInfFam (D := D) θ →
    ∀ (τ : D.what₂.Tau) (A : Submodule ℂ (GA D V → ℂ)), A ≤ GlobalTheory.Mem.AutSpace.SmFun θ V →
    (∀ Z, ∀ f ∈ A, RderC θ V τ Z f ∈ A) → ∀ b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ,
    (∀ Z, ∀ x ∈ A, ∀ y ∈ A, b x (RderC θ V τ Z y) = b (RderC θ V τ ((gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ) x) y) →
    ∀ k, ∀ x ∈ A, ∀ y ∈ A, b x (gelf θ V τ k y) = b (gelf θ V τ k x) y := by
  intro D θ V hθ τ A hAS hA b hb k x hx y hy
  have hu : IsUnit (gramAt D V τ).det := GlobalTheory.SmoothAutCheck.gramAt_unit V τ
  have hM : IsUnit ((gramAt D V τ)⁻¹).det := Matrix.isUnit_nonsing_inv_det_iff.2 hu
  let E : (Fin (k + 1) → Fin V.rank) → Fin (k + 1) → Matrix (Fin V.rank) (Fin V.rank) ℂ :=
    fun idx a => Matrix.single (idx a) (idx (a + 1)) 1
  have hg : ∀ f, gelf θ V τ k f = ∑ idx, wordDer θ V τ (List.ofFn (E idx)) f := by
    intro f
    refine Finset.sum_congr rfl fun idx _ => ?_
    rw [wordDer, ← List.foldr_map (f := RderC θ V τ) (g := fun A acc => A acc), List.map_ofFn]
    rfl
  have hs : ∀ i j, (gramAt D V τ)⁻¹ * Matrix.conjTranspose (Matrix.single i j (1 : ℂ)) * gramAt D V τ =
      -(-((gramAt D V τ)⁻¹ * (Matrix.single i j (1 : ℂ))ᵀ * (gramAt D V τ)⁻¹⁻¹)) := by
    intro i j
    rw [neg_neg, Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.conjTranspose_single, Matrix.transpose_single, star_one]
  have key : ∑ idx, (((List.ofFn (E idx)).reverse.map
        fun Z => (gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ).map (derEnd hθ τ)).prod =
      ∑ idx, ((List.ofFn (E idx)).map (derEnd hθ τ)).prod := by
    have h1 := sum_words_rev (derEnd hθ τ) (gramAt D V τ)⁻¹ hM k
    have e : ∀ idx, ((List.ofFn (E idx)).reverse.map
        fun Z => (gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ).map (derEnd hθ τ) =
        (List.ofFn fun a => derEnd hθ τ (-((gramAt D V τ)⁻¹ * (E idx a)ᵀ * (gramAt D V τ)⁻¹⁻¹))).reverse.map
          fun a => -a := by
      intro idx
      rw [List.map_map, List.map_reverse, List.map_reverse, List.map_ofFn, List.map_ofFn]
      congr 1
      congr 1
      funext a
      simp only [Function.comp_apply, E, hs, map_neg]
    simp only [e, prod_map_neg, List.length_reverse, List.length_ofFn, List.map_ofFn]
    rw [← Finset.smul_sum, h1, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
    rfl
  have hxS : x ∈ GlobalTheory.Mem.AutSpace.SmFun θ V := hAS hx
  have wx : ∀ w, wordDer θ V τ w x = ((w.map (derEnd hθ τ)).prod ⟨x, hxS⟩).1 :=
    fun w => GlobalTheory.RegSch.GelfCyc.wordDer_eq hθ τ w ⟨x, hxS⟩
  have hgx : ∑ idx, wordDer θ V τ ((List.ofFn (E idx)).reverse.map
      fun Z => (gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ) x = gelf θ V τ k x := by
    rw [hg x]
    simp only [wx]
    rw [← Submodule.coe_sum, ← Submodule.coe_sum, ← LinearMap.sum_apply, ← LinearMap.sum_apply, key]
  rw [hg y, map_sum, ← hgx, map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun idx _ => adj_word hA b hb _ x hx y hy
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfandInvariants_symmetric_of_derivativeAdjoint : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D), IsInfFam (D := D) θ →
    ∀ (τ : D.what₂.Tau) (A : Submodule ℂ (GA D V → ℂ)), A ≤ GlobalTheory.Mem.AutSpace.SmFun θ V →
    (∀ Z, ∀ f ∈ A, RderC θ V τ Z f ∈ A) → ∀ b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ,
    (∀ Z, ∀ x ∈ A, ∀ y ∈ A, b x (RderC θ V τ Z y) = b (RderC θ V τ ((gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ) x) y) →
    ∀ k, ∀ x ∈ A, ∀ y ∈ A, b x (gelf θ V τ k y) = b (gelf θ V τ k x) y := by
  atlas_forward_decl GlobalTheory.GelfSymm.gelf_symm
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory.JointSpectral

theorem exists_finset_joint_eigen : ∀ {E ι : Type} [AddCommGroup E] [Module ℂ E] (F : ι → E → E) (Z : Submodule ℂ E), FiniteDimensional ℂ Z →
    (∀ i, ∀ x ∈ Z, F i x ∈ Z) → (∀ i, ∀ x ∈ Z, ∀ y ∈ Z, F i (x + y) = F i x + F i y) →
    (∀ i (a : ℂ), ∀ x ∈ Z, F i (a • x) = a • F i x) → (∀ i j, ∀ x ∈ Z, F i (F j x) = F j (F i x)) →
    ∀ b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ, (∀ x ∈ Z, x ≠ 0 → 0 < (b x x).re) → (∀ x ∈ Z, ∀ y ∈ Z, star (b x y) = b y x) →
    (∀ i, ∀ x ∈ Z, ∀ y ∈ Z, b x (F i y) = b (F i x) y) →
    ∃ C : Finset (ι → ℂ), ∀ x ∈ Z, x ∈ ⨆ c ∈ C, Submodule.span ℂ {h | h ∈ Z ∧ ∀ i, F i h = c i • h} := by
  intro E ι _ _ F Z hfd hmap hadd hsmul hcomm b hpos hsymm hadj
  let T : ι → Module.End ℂ Z := fun i =>
    { toFun := fun x => ⟨F i x, hmap i x x.2⟩
      map_add' := fun x y => Subtype.ext (hadd i x x.2 y y.2)
      map_smul' := fun a x => Subtype.ext (hsmul i a x x.2) }
  let core : InnerProductSpace.Core ℂ Z :=
    { inner := fun x y => b x y
      conj_inner_symm := fun x y => by
        show star (b (y : E) x) = b x y
        exact hsymm y y.2 x x.2
      re_inner_nonneg := fun x => by
        show 0 ≤ (b (x : E) x).re
        by_cases hx : (x : E) = 0
        · rw [hx]; simp
        · exact (hpos x x.2 hx).le
      add_left := fun x y z => by
        show b ((x : E) + y) z = b x z + b y z
        rw [map_add, LinearMap.add_apply]
      smul_left := fun x y r => by
        show b (r • (x : E)) y = starRingEnd ℂ r * b x y
        rw [LinearMap.map_smulₛₗ₂, smul_eq_mul]
      definite := fun x hx => by
        by_contra h0
        have h1 := hpos x x.2 (fun e => h0 (Subtype.ext e))
        have h2 : b (x : E) x = 0 := hx
        rw [h2] at h1
        simp at h1 }
  letI : NormedAddCommGroup Z := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (cd := core)
  letI : InnerProductSpace ℂ Z := InnerProductSpace.ofCore core.toCore
  have hT : ∀ i, (T i).IsSymmetric := fun i x y => (hadj i x x.2 y y.2).symm
  have hC : Pairwise (Function.onFun Commute T) := fun i j _ =>
    LinearMap.ext fun x => Subtype.ext (hcomm i j x x.2)
  have key := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hT hC
  have htop : IsCompactElement (⊤ : Submodule ℂ Z) :=
    (Submodule.fg_iff_compact _).1 (Module.finite_def.1 hfd)
  obtain ⟨s, hs⟩ := CompleteLattice.IsCompactElement.exists_finset_of_le_iSup _ htop
    (fun χ : ι → ℂ => ⨅ i, Module.End.eigenspace (T i) (χ i)) key.ge
  have hle : (⊤ : Submodule ℂ Z) ≤
      (⨆ c ∈ s, Submodule.span ℂ {h | h ∈ Z ∧ ∀ i, F i h = c i • h}).comap Z.subtype := by
    refine hs.trans (iSup₂_le fun c hc y hy => ?_)
    simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hy
    refine Submodule.mem_comap.2 ((le_iSup₂ (f := fun c (_ : c ∈ s) =>
      Submodule.span ℂ {h | h ∈ Z ∧ ∀ i, F i h = c i • h}) c hc) (Submodule.subset_span ⟨y.2, fun i => ?_⟩))
    exact congrArg Subtype.val (hy i)
  exact ⟨s, fun x hx => hle (x := ⟨x, hx⟩) Submodule.mem_top⟩

end GlobalTheory.JointSpectral
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_jointEigenDecomposition_commuting_symmetricOps : ∀ {E ι : Type} [AddCommGroup E] [Module ℂ E] (F : ι → E → E) (Z : Submodule ℂ E), FiniteDimensional ℂ Z →
    (∀ i, ∀ x ∈ Z, F i x ∈ Z) → (∀ i, ∀ x ∈ Z, ∀ y ∈ Z, F i (x + y) = F i x + F i y) →
    (∀ i (a : ℂ), ∀ x ∈ Z, F i (a • x) = a • F i x) → (∀ i j, ∀ x ∈ Z, F i (F j x) = F j (F i x)) →
    ∀ b : E →ₗ⋆[ℂ] E →ₗ[ℂ] ℂ, (∀ x ∈ Z, x ≠ 0 → 0 < (b x x).re) → (∀ x ∈ Z, ∀ y ∈ Z, star (b x y) = b y x) →
    (∀ i, ∀ x ∈ Z, ∀ y ∈ Z, b x (F i y) = b (F i x) y) →
    ∃ C : Finset (ι → ℂ), ∀ x ∈ Z, x ∈ ⨆ c ∈ C, Submodule.span ℂ {h | h ∈ Z ∧ ∀ i, F i h = c i • h} := by
  atlas_forward_decl GlobalTheory.JointSpectral.exists_finset_joint_eigen
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.GKEigen

theorem isGKSub_iSup_eigen : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ → ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ →
    ∀ C : Finset (D.what₂.Tau × ℕ → ℂ), GlobalTheory.CuspGK.IsGKSub θ M (⨆ c ∈ C, Submodule.span ℂ
      {h | h ∈ GlobalTheory.CuspGK.gkGen θ M ψ ∧ ∀ i : D.what₂.Tau × ℕ, gelf θ V i.1 i.2 h = c i • h}) := by
  intro D θ V S M hθ ψ hψ C
  have hG := GlobalTheory.CuspGK.isGKSub_gkGen θ M ψ
  have hsm : ∀ f ∈ GlobalTheory.CuspGK.gkGen θ M ψ, f ∈ GlobalTheory.Mem.AutSpace.SmFun θ V := fun f hf =>
    (GlobalTheory.KTypeAdm.isAutFunSm_of_mem_gkGen θ M hθ hψ f hf).smooth
  set T : Set (GA D V → ℂ) := ⋃ c ∈ C,
    {h | h ∈ GlobalTheory.CuspGK.gkGen θ M ψ ∧ ∀ i : D.what₂.Tau × ℕ, gelf θ V i.1 i.2 h = c i • h} with hTdef
  have hspan : (⨆ c ∈ C, Submodule.span ℂ
      {h | h ∈ GlobalTheory.CuspGK.gkGen θ M ψ ∧ ∀ i : D.what₂.Tau × ℕ, gelf θ V i.1 i.2 h = c i • h}) =
      Submodule.span ℂ T := by
    rw [hTdef, Submodule.span_iUnion₂]
  rw [hspan]
  have hTG : T ⊆ GlobalTheory.CuspGK.gkGen θ M ψ := by
    intro h hh
    rw [hTdef, Set.mem_iUnion₂] at hh
    obtain ⟨c, _, hh, _⟩ := hh
    exact hh
  have hSG : Submodule.span ℂ T ≤ GlobalTheory.CuspGK.gkGen θ M ψ := Submodule.span_le.2 hTG
  have hTk : ∀ τ g, GlobalTheory.CuspGK.InK M τ g → ∀ h ∈ T, rTr V (atTau θ V τ g) h ∈ T := by
    intro τ g hg h hh
    rw [hTdef, Set.mem_iUnion₂] at hh ⊢
    obtain ⟨c, hc, hhG, he⟩ := hh
    refine ⟨c, hc, hG.k τ g hg h hhG, fun i => ?_⟩
    rw [GlobalTheory.RegSch.CentreRight.gelf_rTr_all hθ _ i.1 i.2 (hsm h hhG), he i]
    rfl
  have hTl : ∀ τ, ∀ X ∈ lieAt V τ, ∀ h ∈ T, Rder θ V τ X h ∈ T := by
    intro τ X hX h hh
    rw [hTdef, Set.mem_iUnion₂] at hh ⊢
    obtain ⟨c, hc, hhG, he⟩ := hh
    refine ⟨c, hc, hG.lie τ X hX h hhG, fun i => ?_⟩
    rw [GlobalTheory.CuspLie.gelf_Rder hθ hX (hsm h hhG) i.1 i.2, he i, GlobalTheory.Mem.AutSpace.Rder_smul]
  refine ⟨fun τ g hg f hf => ?_, fun τ X hX f hf => ?_⟩
  · induction hf using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (hTk τ g hg x hx)
    | zero => exact (Submodule.span ℂ T).zero_mem
    | add x y _ _ hx hy => exact (Submodule.span ℂ T).add_mem hx hy
    | smul a x _ hx => exact (Submodule.span ℂ T).smul_mem a hx
  · induction hf using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (hTl τ X hX x hx)
    | zero =>
      rw [Formalism.IndefR.Mult.rder_zero θ V τ X]
      exact (Submodule.span ℂ T).zero_mem
    | add x y hx' hy' hx hy =>
      rw [GlobalTheory.Mem.AutSpace.Rder_add (hsm x (hSG hx')) (hsm y (hSG hy')) hX]
      exact (Submodule.span ℂ T).add_mem hx hy
    | smul a x _ hx =>
      rw [GlobalTheory.Mem.AutSpace.Rder_smul]
      exact (Submodule.span ℂ T).smul_mem a hx

end GlobalTheory.GKEigen

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGKSubmodule_iSup_gelfandJointEigenspaces : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ → ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ →
    ∀ C : Finset (D.what₂.Tau × ℕ → ℂ), GlobalTheory.CuspGK.IsGKSub θ M (⨆ c ∈ C, Submodule.span ℂ
      {h | h ∈ GlobalTheory.CuspGK.gkGen θ M ψ ∧ ∀ i : D.what₂.Tau × ℕ, gelf θ V i.1 i.2 h = c i • h}) := by
  atlas_forward_decl GlobalTheory.GKEigen.isGKSub_iSup_eigen
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory.KTypeGelf

theorem gelf_mem_typeSpan : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ → ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ →
    ∀ (Y₀ : Submodule ℂ (GA D V → ℂ)) (τ : D.what₂.Tau) (k : ℕ),
    ∀ f ∈ GlobalTheory.KTypeProj.typeSpan (GlobalTheory.KTypeProj.rhoK θ M) Y₀ (GlobalTheory.CuspGK.gkGen θ M ψ),
      gelf θ V τ k f ∈ GlobalTheory.KTypeProj.typeSpan (GlobalTheory.KTypeProj.rhoK θ M) Y₀ (GlobalTheory.CuspGK.gkGen θ M ψ) := by
  intro D θ V S M hθ ψ hψ Y₀ τ k
  set G := GlobalTheory.CuspGK.gkGen θ M ψ with hGdef
  set ρ := GlobalTheory.KTypeProj.rhoK θ M with hρ
  have hGsm : ∀ f ∈ G, f ∈ GlobalTheory.Mem.AutSpace.SmFun θ V := fun f hf =>
    fun k τs Xs h g => (GlobalTheory.KTypeAdm.isAutFunSm_of_mem_gkGen θ M hθ hψ f hf).smooth k τs Xs h g
  have hL := GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) τ k

  let g0 : GlobalTheory.Mem.AutSpace.SmFun θ V →ₗ[ℂ] (GA D V → ℂ) :=
    { toFun := fun φ => gelf θ V τ k φ
      map_add' := fun φ ψ' => hL.add _ φ.2 _ ψ'.2
      map_smul' := fun c φ => hL.smul c φ }
  obtain ⟨L, hLe⟩ := LinearMap.exists_extend g0
  have hLa : ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, L φ = gelf θ V τ k φ := fun φ hφ => by
    have := congrArg (fun F => F ⟨φ, hφ⟩) hLe
    simpa [g0] using this
  have hgel0 : gelf θ V τ k 0 = 0 := by
    have := hL.smul 0 0
    simpa using this
  let Q : Submodule ℂ (GA D V → ℂ) :=
    { carrier := {f | f ∈ G ∧ gelf θ V τ k f ∈ GlobalTheory.KTypeProj.typeSpan ρ Y₀ G}
      add_mem' := fun {a b} ha hb => by
        refine ⟨G.add_mem ha.1 hb.1, ?_⟩
        rw [hL.add a (hGsm a ha.1) b (hGsm b hb.1)]
        exact Submodule.add_mem _ ha.2 hb.2
      zero_mem' := ⟨G.zero_mem, by rw [hgel0]; exact Submodule.zero_mem _⟩
      smul_mem' := fun c f hf => by
        refine ⟨G.smul_mem c hf.1, ?_⟩
        rw [hL.smul c f]
        exact Submodule.smul_mem _ c hf.2 }
  have hle : GlobalTheory.KTypeProj.typeSpan ρ Y₀ G ≤ Q := by
    refine iSup₂_le fun T hT => ?_
    rintro _ ⟨w, hw, rfl⟩
    have hTw : T w ∈ G := hT.1 ⟨w, hw, rfl⟩
    refine ⟨hTw, ?_⟩
    have hmap : Y₀.map (L ∘ₗ T) ≤ G := by
      rintro _ ⟨v, hv, rfl⟩
      have hTv : T v ∈ G := hT.1 ⟨v, hv, rfl⟩
      show L (T v) ∈ G
      rw [hLa _ (hGsm _ hTv)]
      exact GlobalTheory.KTypeAdm.gelf_mem_of_isGKSub θ M (GlobalTheory.CuspGK.isGKSub_gkGen θ M ψ) τ k _ hTv
    have hcomm : ∀ i, ∀ v ∈ Y₀, (L ∘ₗ T) (ρ i v) = ρ i ((L ∘ₗ T) v) := by
      intro i v hv
      have hTv : T v ∈ G := hT.1 ⟨v, hv, rfl⟩
      have hs := hGsm _ hTv
      simp only [LinearMap.comp_apply]
      rw [hT.2 i v hv, hLa _ (hs), hρ, GlobalTheory.KTypeProj.rhoK, GlobalTheory.KTypeProj.rTrL_apply, GlobalTheory.KTypeProj.rTrL_apply,
        hLa _ (GlobalTheory.RegSch.CentreRight.rTr_mem_all hθ _ hs), GlobalTheory.RegSch.CentreRight.gelf_rTr_all hθ _ τ k hs]
    have := GlobalTheory.KTypeProj.map_le_typeSpan ρ (L ∘ₗ T) hmap hcomm ⟨w, hw, rfl⟩
    simpa [hLa _ (hGsm _ hTw)] using this
  intro f hf
  exact (hle hf).2

end GlobalTheory.KTypeGelf
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gelfandInvariant_mem_intertwinedTypeSpan : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ → ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ →
    ∀ (Y₀ : Submodule ℂ (GA D V → ℂ)) (τ : D.what₂.Tau) (k : ℕ),
    ∀ f ∈ GlobalTheory.KTypeProj.typeSpan (GlobalTheory.KTypeProj.rhoK θ M) Y₀ (GlobalTheory.CuspGK.gkGen θ M ψ),
      gelf θ V τ k f ∈ GlobalTheory.KTypeProj.typeSpan (GlobalTheory.KTypeProj.rhoK θ M) Y₀ (GlobalTheory.CuspGK.gkGen θ M ψ) := by
  atlas_forward_decl GlobalTheory.KTypeGelf.gelf_mem_typeSpan
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory

theorem mem_iSup_jointEigen_inf_of_stable : ∀ {E ι : Type} [AddCommGroup E] [Module ℂ E] (F : ι → E → E) (G P : Submodule ℂ E) (C : Finset (ι → ℂ)),
    (∀ i, ∀ x ∈ G, F i x ∈ G) → (∀ i, ∀ x ∈ G, ∀ y ∈ G, F i (x + y) = F i x + F i y) →
    (∀ i (a : ℂ), ∀ x ∈ G, F i (a • x) = a • F i x) → P ≤ G → (∀ i, ∀ x ∈ P, F i x ∈ P) →
    (∀ x ∈ G, x ∈ ⨆ c ∈ C, Submodule.span ℂ {h | h ∈ G ∧ ∀ i, F i h = c i • h}) →
    ∀ x ∈ P, x ∈ ⨆ c ∈ C, Submodule.span ℂ {h | h ∈ P ∧ ∀ i, F i h = c i • h} := by
  intro E ι _ _ F G P C hFG hadd hsmul hPG hFP hdec
  have hF0 : ∀ i, F i 0 = 0 := by
    intro i
    have := hsmul i 0 0 G.zero_mem
    simpa using this
  obtain ⟨V, hV⟩ : ∃ V : (ι → ℂ) → Submodule ℂ E,
      ∀ c x, x ∈ V c ↔ (x ∈ G ∧ ∀ i, F i x = c i • x) :=
    ⟨fun c =>
      { carrier := {h | h ∈ G ∧ ∀ i, F i h = c i • h}
        add_mem' := by
          rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
          refine ⟨G.add_mem hx hy, fun i => ?_⟩
          rw [hadd i x hx y hy, hx' i, hy' i, smul_add]
        zero_mem' := ⟨G.zero_mem, fun i => by rw [hF0 i, smul_zero]⟩
        smul_mem' := by
          rintro a x ⟨hx, hx'⟩
          refine ⟨G.smul_mem a hx, fun i => ?_⟩
          rw [hsmul i a x hx, hx' i]
          exact smul_comm _ _ _ }, fun c x => Iff.rfl⟩
  have hVG : ∀ c, V c ≤ G := fun c x hx => ((hV c x).1 hx).1
  have hSG : ∀ s : Finset (ι → ℂ), (⨆ c ∈ s, V c) ≤ G := fun s => iSup₂_le fun c _ => hVG c
  have hmemS : ∀ (s : Finset (ι → ℂ)) c, c ∈ s → V c ≤ ⨆ c ∈ s, V c := fun s c hc =>
    le_iSup₂_of_le (f := fun c (_ : c ∈ s) => V c) c hc le_rfl
  have hT : ∀ (i : ι) (b : ℂ) (s : Finset (ι → ℂ)), ∀ z ∈ ⨆ c ∈ s, V c,
      F i z - b • z ∈ ⨆ c ∈ s, V c := by
    intro i b s
    obtain ⟨M, hM⟩ : ∃ M : Submodule ℂ E,
        ∀ v, v ∈ M ↔ (v ∈ G ∧ F i v - b • v ∈ ⨆ c ∈ s, V c) :=
      ⟨{ carrier := {v | v ∈ G ∧ F i v - b • v ∈ ⨆ c ∈ s, V c}
         add_mem' := by
           rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
           refine ⟨G.add_mem hx hy, ?_⟩
           have : F i (x + y) - b • (x + y) = (F i x - b • x) + (F i y - b • y) := by
             rw [hadd i x hx y hy, smul_add]; abel
           rw [this]; exact Submodule.add_mem _ hx' hy'
         zero_mem' := ⟨G.zero_mem, by simp [hF0 i]⟩
         smul_mem' := by
           rintro a x ⟨hx, hx'⟩
           refine ⟨G.smul_mem a hx, ?_⟩
           have : F i (a • x) - b • (a • x) = a • (F i x - b • x) := by
             rw [hsmul i a x hx, smul_sub, smul_comm b a x]
           rw [this]; exact Submodule.smul_mem _ a hx' }, fun v => Iff.rfl⟩
    have hle : (⨆ c ∈ s, V c) ≤ M := iSup₂_le fun c hc v hv => by
      rw [hM]
      obtain ⟨hvG, hv'⟩ := (hV c v).1 hv
      refine ⟨hvG, ?_⟩
      rw [hv' i, ← sub_smul]
      exact hmemS s c hc ((V c).smul_mem _ hv)
    intro z hz
    exact ((hM z).1 (hle hz)).2
  have hB : ∀ (a : ι → ℂ) (s : Finset (ι → ℂ)), a ∉ s → ∀ y ∈ V a, ∀ z ∈ ⨆ c ∈ s, V c,
      y + z ∈ P → y ∈ P := by
    intro a s
    induction s using Finset.induction_on with
    | empty =>
      intro _ y _ z hz hyz
      simp at hz
      rw [hz, add_zero] at hyz; exact hyz
    | insert b t hbt ih =>
      intro ha y hy z hz hyz
      rw [Finset.mem_insert, not_or] at ha
      obtain ⟨hab, hat⟩ := ha
      rw [Finset.iSup_insert, Submodule.mem_sup] at hz
      obtain ⟨zb, hzb, zt, hzt, rfl⟩ := hz
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hab
      obtain ⟨hyG, hy'⟩ := (hV a y).1 hy
      obtain ⟨hzbG, hzb'⟩ := (hV b zb).1 hzb
      have hztG := hSG t hzt
      have hP1 : F i (y + (zb + zt)) - b i • (y + (zb + zt)) ∈ P :=
        P.sub_mem (hFP i _ hyz) (P.smul_mem _ hyz)
      have heq : F i (y + (zb + zt)) - b i • (y + (zb + zt))
          = (a i - b i) • y + (F i zt - b i • zt) := by
        rw [hadd i y hyG _ (G.add_mem hzbG hztG), hadd i zb hzbG zt hztG, hy' i, hzb' i]
        simp only [smul_add, sub_smul]; abel
      rw [heq] at hP1
      have hy2 : (a i - b i) • y ∈ V a := (V a).smul_mem _ hy
      have h3 := ih hat _ hy2 _ (hT i (b i) t zt hzt) hP1
      have hne : a i - b i ≠ 0 := sub_ne_zero.2 hi
      have h4 := P.smul_mem (a i - b i)⁻¹ h3
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h4
  have hspan : ∀ c, Submodule.span ℂ {h | h ∈ G ∧ ∀ i, F i h = c i • h} = V c := fun c =>
    le_antisymm (Submodule.span_le.2 fun x hx => (hV c x).2 hx)
      fun x hx => Submodule.subset_span ((hV c x).1 hx)
  have hmain : ∀ s : Finset (ι → ℂ), ∀ x ∈ P, x ∈ ⨆ c ∈ s, V c →
      x ∈ ⨆ c ∈ s, Submodule.span ℂ {h | h ∈ P ∧ ∀ i, F i h = c i • h} := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x _ hx; simpa using hx
    | insert a s has ih =>
      intro x hxP hx
      rw [Finset.iSup_insert, Submodule.mem_sup] at hx
      obtain ⟨y, hy, z, hz, rfl⟩ := hx
      have hyP : y ∈ P := hB a s has y hy z hz hxP
      have hzP : z ∈ P := by
        have := P.sub_mem hxP hyP; simpa using this
      rw [Finset.iSup_insert]
      exact Submodule.mem_sup.2 ⟨y, Submodule.subset_span ⟨hyP, ((hV a y).1 hy).2⟩, z, ih z hzP hz, rfl⟩
  intro x hx
  have h := hdec x (hPG hx)
  simp only [hspan] at h
  exact hmain C x hx h

end GlobalTheory
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_iSup_jointEigenspaces_inf_of_stableSubmodule : ∀ {E ι : Type} [AddCommGroup E] [Module ℂ E] (F : ι → E → E) (G P : Submodule ℂ E) (C : Finset (ι → ℂ)),
    (∀ i, ∀ x ∈ G, F i x ∈ G) → (∀ i, ∀ x ∈ G, ∀ y ∈ G, F i (x + y) = F i x + F i y) →
    (∀ i (a : ℂ), ∀ x ∈ G, F i (a • x) = a • F i x) → P ≤ G → (∀ i, ∀ x ∈ P, F i x ∈ P) →
    (∀ x ∈ G, x ∈ ⨆ c ∈ C, Submodule.span ℂ {h | h ∈ G ∧ ∀ i, F i h = c i • h}) →
    ∀ x ∈ P, x ∈ ⨆ c ∈ C, Submodule.span ℂ {h | h ∈ P ∧ ∀ i, F i h = c i • h} := by
  atlas_forward_decl GlobalTheory.mem_iSup_jointEigen_inf_of_stable
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

theorem GlobalTheory.KTypeAdm.finiteDimensional_typeSpan : GlobalTheory.FunPr.Hypotheses₂ → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    ∀ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W → ψ ∈ W → GlobalTheory.KTypeProj.KStable θ M W →
    ∀ b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ,
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, x ≠ 0 → 0 < (b x x).re) →
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ, star (b x y) = b y x) →
      (∀ τ g, GlobalTheory.CuspGK.InK M τ g → ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (rTr V (atTau θ V τ g) y) = b (rTr V (atTau θ V τ g⁻¹) x) y) →
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) →
    FiniteDimensional ℂ (GlobalTheory.KTypeProj.typeSpan (GlobalTheory.KTypeProj.rhoK θ M) (W ⊓ GlobalTheory.CuspGK.gkGen θ M ψ)
      (GlobalTheory.CuspGK.gkGen θ M ψ)) := by
  intro hP D θ V S M hθ ψ hψ _hcusp W hW hψW hWK b hpos hherm _hK hskew
  set G := GlobalTheory.CuspGK.gkGen θ M ψ with hGdef
  have hsm := GlobalTheory.KTypeAdm.isAutFunSm_of_mem_gkGen θ M hθ hψ
  obtain ⟨U, hU, hlev⟩ := GlobalTheory.KTypeAdm.level_gkGen θ M hψ
  have hY : GlobalTheory.KTypeProj.KStable θ M (W ⊓ G) :=
    GlobalTheory.KTypeProj.kStable_inf θ M hWK (GlobalTheory.KTypeProj.kStable_gkGen θ M ψ)
  haveI hYf : FiniteDimensional ℂ ↥(W ⊓ G) := Submodule.finiteDimensional_of_le inf_le_left
  have hcont : ∀ f ∈ W ⊓ G, Continuous f := fun f hf => (hsm f hf.2).cont
  choose ρ hρc hρT using GlobalTheory.T.exists_continuousRep_rightTranslation_maxCompactStable θ V S M hθ (W ⊓ G) hYf hY hcont
  have hGK := GlobalTheory.CuspGK.isGKSub_gkGen θ M ψ
  have hGsm : G ≤ GlobalTheory.Mem.AutSpace.SmFun θ V := fun f hf => (hsm f hf).smooth
  have hGC : ∀ τ Z, ∀ f ∈ G, RderC θ V τ Z f ∈ G := fun τ Z f hf => by
    obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem (V := V) τ Z
    exact G.add_mem (hGK.lie τ _ h1 f hf) (G.smul_mem _ (hGK.lie τ _ h2 f hf))
  have hsym : ∀ τ k, ∀ x ∈ G, ∀ y ∈ G, b x (gelf θ V τ k y) = b (gelf θ V τ k x) y := fun τ =>
    GlobalTheory.T.gelfandInvariants_symmetric_of_derivativeAdjoint θ V hθ τ G hGsm (hGC τ) b (GlobalTheory.T.complexDerivative_adjoint_of_skew_form θ V τ G b (hskew τ))
  let F : D.what₂.Tau × ℕ → (GA D V → ℂ) → (GA D V → ℂ) := fun i => gelf θ V i.1 i.2
  have hFG : ∀ i, ∀ x ∈ G, F i x ∈ G := fun i => GlobalTheory.KTypeAdm.gelf_mem_of_isGKSub θ M hGK i.1 i.2
  have hFadd : ∀ i, ∀ x ∈ G, ∀ y ∈ G, F i (x + y) = F i x + F i y := fun i x hx y hy =>
    (GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) i.1 i.2).add x (hGsm hx) y (hGsm hy)
  have hFsmul : ∀ i (a : ℂ), ∀ x ∈ G, F i (a • x) = a • F i x := fun i a x _ =>
    (GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) i.1 i.2).smul a x
  have hFcomm : ∀ i j, ∀ x ∈ G, F i (F j x) = F j (F i x) := fun i j x hx =>
    GlobalTheory.CentreComm.comm_gelf (GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) i.1 i.2)
      (fun Z => GlobalTheory.CentreComm.gelf_RderC hθ i.1 j.1 i.2 Z) j.2 x (hGsm hx)
  obtain ⟨Wz, hWz, hψz, hWzst⟩ := hψ.zfin
  haveI := hWz
  haveI : FiniteDimensional ℂ ↥(Wz ⊓ G) := Submodule.finiteDimensional_of_le inf_le_left
  obtain ⟨C, hC⟩ := GlobalTheory.T.exists_jointEigenDecomposition_commuting_symmetricOps F (Wz ⊓ G) inferInstance
    (fun i x hx => ⟨hWzst i.1 i.2 x hx.1, hFG i x hx.2⟩) (fun i x hx y hy => hFadd i x hx.2 y hy.2)
    (fun i a x hx => hFsmul i a x hx.2) (fun i j x hx => hFcomm i j x hx.2) b (fun x hx => hpos x hx.2)
    (fun x hx y hy => hherm x hx.2 y hy.2) (fun i x hx y hy => hsym i.1 i.2 x hx.2 y hy.2)
  have hGS : G ≤ ⨆ c ∈ C, Submodule.span ℂ
      {h | h ∈ G ∧ ∀ i : D.what₂.Tau × ℕ, gelf θ V i.1 i.2 h = c i • h} := by
    refine GlobalTheory.CuspGK.gkGen_le θ M ?_ (GlobalTheory.T.isGKSubmodule_iSup_gelfandJointEigenspaces θ V S M hθ ψ hψ C)
    have := hC ψ ⟨hψz, GlobalTheory.CuspGK.mem_gkGen θ M ψ⟩
    refine (iSup₂_mono fun c _ => Submodule.span_mono ?_) this
    exact fun h hh => ⟨hh.1.2, hh.2⟩
  set P := GlobalTheory.KTypeProj.typeSpan (GlobalTheory.KTypeProj.rhoK θ M) (W ⊓ G) G with hPdef
  have hPG : P ≤ G := GlobalTheory.KTypeProj.typeSpan_le _ _ _
  have hPst : ∀ i, ∀ x ∈ P, F i x ∈ P := fun i => GlobalTheory.T.gelfandInvariant_mem_intertwinedTypeSpan θ V S M hθ ψ hψ (W ⊓ G) i.1 i.2
  have hdec := GlobalTheory.T.mem_iSup_jointEigenspaces_inf_of_stableSubmodule F G P C hFG hFadd hFsmul hPG hPst (fun x hx => hGS hx)
  have htype : ∀ τ, ∀ h ∈ P, GlobalTheory.Published.AutFin.HasTypeAt θ V τ (M.ε τ) (M.fr τ) (ρ τ) h := by
    intro τ
    let Q : Submodule ℂ (GA D V → ℂ) :=
      { carrier := {h | GlobalTheory.Published.AutFin.HasTypeAt θ V τ (M.ε τ) (M.fr τ) (ρ τ) h}
        add_mem' := fun ha hb x => Submodule.add_mem _ (ha x) (hb x)
        zero_mem' := fun x => Submodule.zero_mem _
        smul_mem' := fun c f hf x => Submodule.smul_mem _ c (hf x) }
    have hPQ : P ≤ Q := by
      refine iSup₂_le fun T hT => ?_
      rintro _ ⟨w, hw, rfl⟩
      exact hρT τ T hT.2 ⟨w, hw⟩
    exact fun h hh => hPQ hh
  have hfr : GlobalTheory.Published.AutFin.IsFrameFam V M.ε M.fr := fun τ => ⟨M.fr_unit τ, M.fr_gram τ⟩
  have hfin : ∀ c : D.what₂.Tau × ℕ → ℂ, FiniteDimensional ℂ
      (Submodule.span ℂ (GlobalTheory.Published.AutFin.forms θ V U M.ε M.fr ρ (fun τ k => c (τ, k)))) := fun c =>
    hP.harishChandraFinite D θ hθ V U hU M.ε M.fr hfr (fun _ => ↥(W ⊓ G)) ρ hρc _
  have hle : P ≤ C.sup fun c =>
      Submodule.span ℂ (GlobalTheory.Published.AutFin.forms θ V U M.ε M.fr ρ (fun τ k => c (τ, k))) := by
    intro x hx
    have := hdec x hx
    rw [← Finset.sup_eq_iSup] at this
    have key : ∀ c : D.what₂.Tau × ℕ → ℂ, Submodule.span ℂ {h | h ∈ P ∧ ∀ i, F i h = c i • h} ≤
        Submodule.span ℂ (GlobalTheory.Published.AutFin.forms θ V U M.ε M.fr ρ (fun τ k => c (τ, k))) := fun c =>
      Submodule.span_mono (by
        rintro h ⟨hP', hc⟩
        exact ⟨hsm h (hPG hP'), fun u hu hu' g => hlev h (hPG hP') u hu hu' g, fun τ => htype τ h hP',
          fun τ k => hc (τ, k)⟩)
    exact Finset.sup_mono_fun (fun c _ => key c) this
  haveI : ∀ c : D.what₂.Tau × ℕ → ℂ, FiniteDimensional ℂ
      (Submodule.span ℂ (GlobalTheory.Published.AutFin.forms θ V U M.ε M.fr ρ (fun τ k => c (τ, k)))) := hfin
  exact Submodule.finiteDimensional_of_le hle

end
end
