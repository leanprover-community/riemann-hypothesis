import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalPointOriginSmoothCommGroupScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedGroupPointSameDerivations
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Formalism.LocalToGlobal.ProjectiveLattices.PowMapMemOfPowMulMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorOnRingConjPowFractionField
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorValueAtPointEqRingOperator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorActsOnFourierTermsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeneratingFramesComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesGeneratingAtPoint
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonOfProdLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorsKodairaSpencerFormalPointValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorSymbolUniquePrincipalPolarisation
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTangentBasisOfRaynaudBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantTangentBasisRaynaudExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceOfSmoothOfGeometricallyConnected
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFrameBaseHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTripleAbelianLocusProperRelAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixTransposeEqAtPolarizedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerAbelianLocusChartRing

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heatOperatorOnRing_conj_pow_fractionField : ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] (n : ℕ) (d : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (δ : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (Θ : Matrix (Fin n) (Fin n) (FractionRing Ω)), Θᵀ = Θ → (2 : FractionRing Ω) ≠ 0 → ∀ (u : Fin n → FractionRing Ω) (p p' c : FractionRing Ω), c ≠ 0 → ∃ (d' : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u'' : Fin n → FractionRing Ω) (q q' : FractionRing Ω), (∀ y, (∀ a, δ a y = 0) → d' y = d y) ∧ ∀ (k : ℕ) (f : FractionRing Ω), ringOp ⇑d (fun a => ⇑(δ a)) Θ u p p' k (c ^ k * f) = c ^ k * ringOp ⇑d' (fun a => ⇑(δ a)) Θ u'' q q' k f := by
  first | exact @GlobalTheory.Heat.ringOp_conj_pow | exact GlobalTheory.Heat.ringOp_conj_pow | (intros; apply GlobalTheory.Heat.ringOp_conj_pow <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat

theorem sval_smul_add_smul {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s t : LB.Sec (LB.LinComb L φ ε)) (a b : Γ(Y, ⊤)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (a • s + b • t) r z J = gs r z ⊤ a * sval s r z J + gs r z ⊤ b * sval t r z J := by
  have hm := hJ.mem φ r
  exact (gs_add r z _ hm _ _).trans (congrArg₂ (· + ·)
    ((gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm a)))
    ((gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm b))))

theorem gs_base_fn {R Ω : Type} [CommRing R] [CommRing Ω] {Y Z : Scheme.{0}} (p : Y ⟶ Sp R) (φ : R →+* Ω)
    (x : Sp Ω ⟶ Y) (h : x ≫ p = spMap φ) (r : Z ⟶ Sp Ω) (z : Z) (a : R) :
    gs (r ≫ x) z ⊤ (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) =
      gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (φ a)) := by
  have e₁ := gs_pull (r ≫ x) p z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)
  have e₂ := gs_pull r (spMap φ) z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)
  rw [Category.assoc, h] at e₁
  refine e₁.trans (e₂.symm.trans (congrArg (gs r z ⊤) ?_))
  exact (congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))).symm

theorem exists_isValue_lin : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) (L : LB G.left) (Ω : Type) [CommRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ G.left), x' ≫ G.hom = spMap φ → ∀ (g : GlobalTheory.RayEv.Transport.Frame L (x' ≫ 𝟙 G.left)) (k : ℕ) (σ₁ σ₂ : SecM (𝟙 G.left) L k) (ω₁ ω₂ : Ω) (a b : R), IsValue (𝟙 _) L x' g k σ₁ ω₁ → IsValue (𝟙 _) L x' g k σ₂ ω₂ → ∃ σ : SecM (𝟙 G.left) L k, IsValue (𝟙 _) L x' g k σ (φ a * ω₁ + φ b * ω₂) := by
  intro R _ G L Ω _ φ x' h g k σ₁ σ₂ ω₁ ω₂ a b h₁ h₂
  refine ⟨(show Γ(G.left, ⊤) from G.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) • σ₁ +
    (show Γ(G.left, ⊤) from G.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom b)) • σ₂,
    fun Z r z J hJ => ?_⟩
  refine (sval_smul_add_smul σ₁ σ₂ _ _ (r ≫ x') z hJ).trans ?_
  rw [h₁ Z r z J hJ, h₂ Z r z J hJ, map_add, map_mul, map_mul, gs_add r z ⊤ trivial, gs_mul r z ⊤ trivial,
    gs_mul r z ⊤ trivial, ← gs_base_fn G.hom φ x' h r z a, ← gs_base_fn G.hom φ x' h r z b, add_mul, _root_.mul_assoc,
    _root_.mul_assoc]

end GlobalTheory.Heat
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionValueInFrame_linearCombination : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) (L : LB G.left) (Ω : Type) [CommRing Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ G.left), x' ≫ G.hom = spMap φ → ∀ (g : GlobalTheory.RayEv.Transport.Frame L (x' ≫ 𝟙 G.left)) (k : ℕ) (σ₁ σ₂ : SecM (𝟙 G.left) L k) (ω₁ ω₂ : Ω) (a b : R), IsValue (𝟙 _) L x' g k σ₁ ω₁ → IsValue (𝟙 _) L x' g k σ₂ ω₂ → ∃ σ : SecM (𝟙 G.left) L k, IsValue (𝟙 _) L x' g k σ (φ a * ω₁ + φ b * ω₂) := by
  atlas_forward_decl GlobalTheory.Heat.exists_isValue_lin
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatValues

theorem ringOp_mem {Ω : Type} [CommRing Ω] (J : Ideal Ω) {n : ℕ} (d : Derivation ℤ Ω Ω)
    (δ : Fin n → Derivation ℤ Ω Ω) (Θ : Matrix (Fin n) (Fin n) Ω) (u : Fin n → Ω) (p p' : Ω) (k : ℕ)
    (N : ℕ) (y : Ω) (hy : y ∈ J ^ (N + 2)) :
    ringOp ⇑d (fun a => ⇑(δ a)) Θ u p p' k y ∈ J ^ N := by
  have h1 : ∀ (D : Derivation ℤ Ω Ω) (x : Ω), x ∈ J ^ (N + 1 + 1) → D x ∈ J ^ (N + 1) := fun D x hx =>
    GlobalTheory.SymbolOne.deriv_mem_pow D J (N + 1) x hx
  have h2 : ∀ (D : Derivation ℤ Ω Ω) (x : Ω), x ∈ J ^ (N + 1) → D x ∈ J ^ N := fun D x hx =>
    GlobalTheory.SymbolOne.deriv_mem_pow D J N x hx
  have le1 : J ^ (N + 1) ≤ J ^ N := Ideal.pow_le_pow_right (Nat.le_succ N)
  have le2 : J ^ (N + 2) ≤ J ^ N := Ideal.pow_le_pow_right (by omega)
  unfold ringOp
  refine add_mem (add_mem (sub_mem ?_ ?_) ?_) ?_
  · exact Ideal.mul_mem_left _ _ (le1 (h1 d y hy))
  · exact Ideal.sum_mem _ fun a _ => Ideal.sum_mem _ fun b _ => Ideal.mul_mem_left _ _ (h2 _ _ (h1 _ _ hy))
  · exact Ideal.mul_mem_left _ _ (Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (le1 (h1 _ _ hy)))
  · exact Ideal.mul_mem_left _ _ (le2 hy)

theorem ringOp_add {Ω : Type} [CommRing Ω] {n : ℕ} (d : Derivation ℤ Ω Ω)
    (δ : Fin n → Derivation ℤ Ω Ω) (Θ : Matrix (Fin n) (Fin n) Ω) (u : Fin n → Ω) (p p' : Ω) (k : ℕ) (f g : Ω) :
    ringOp ⇑d (fun a => ⇑(δ a)) Θ u p p' k (f + g) =
      ringOp ⇑d (fun a => ⇑(δ a)) Θ u p p' k f + ringOp ⇑d (fun a => ⇑(δ a)) Θ u p p' k g := by
  unfold ringOp
  simp only [map_add, mul_add, Finset.sum_add_distrib]
  ring

theorem ringOp_mul {Ω : Type} [CommRing Ω] {n : ℕ} (d : Derivation ℤ Ω Ω)
    (δ : Fin n → Derivation ℤ Ω Ω) (Θ : Matrix (Fin n) (Fin n) Ω) (u : Fin n → Ω) (p p' : Ω) (k : ℕ) (c f : Ω)
    (hc : ∀ a, δ a c = 0) :
    ringOp ⇑d (fun a => ⇑(δ a)) Θ u p p' k (c * f) =
      c * ringOp ⇑d (fun a => ⇑(δ a)) Θ u p p' k f + 2 * (k : Ω) * d c * f := by
  have e1 : ∀ a x, δ a (c * x) = c * δ a x := fun a x => by
    rw [Derivation.leibniz, hc, smul_zero, add_zero, smul_eq_mul]
  have e2 : ∀ a b, Θ a b * δ a (δ b (c * f)) = c * (Θ a b * δ a (δ b f)) := fun a b => by
    rw [e1, e1]; ring
  have e3 : ∀ a, u a * δ a (c * f) = c * (u a * δ a f) := fun a => by rw [e1]; ring
  have e4 : d (c * f) = c * d f + f * d c := by rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  unfold ringOp
  simp only [e2, e3, ← Finset.mul_sum, e4]
  ring

theorem eq_of_adic {Ω Idx : Type} [CommRing Ω] (J : Ideal Ω) [IsHausdorff J Ω] (T : Ω →+ Ω)
    (hT : ∀ N y, y ∈ J ^ (N + 2) → T y ∈ J ^ N) (c s s' : Ω) (t t' : Idx → Ω)
    (ht : ∀ α, t' α = c * T (t α))
    (hs : ∀ e : ℕ, ∃ S : Finset Idx, (∀ α ∉ S, t α ∈ J ^ (e + 1)) ∧ s - ∑ α ∈ S, t α ∈ J ^ (e + 1))
    (hs' : ∀ e : ℕ, ∃ S : Finset Idx, (∀ α ∉ S, t' α ∈ J ^ (e + 1)) ∧ s' - ∑ α ∈ S, t' α ∈ J ^ (e + 1)) :
    s' = c * T s := by
  classical
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := J) _ fun N => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  obtain ⟨S, hS1, hS2⟩ := hs (N + 1)
  obtain ⟨S', hS1', hS2'⟩ := hs' (N + 1)
  have split : ∀ (v : Idx → Ω) (A B : Finset Idx), ∑ α ∈ A ∪ B, v α = ∑ α ∈ A, v α + ∑ α ∈ B \ A, v α := by
    intro v A B
    rw [← Finset.union_sdiff_self_eq_union, Finset.sum_union Finset.disjoint_sdiff]
  have m1 : s - ∑ α ∈ S ∪ S', t α ∈ J ^ (N + 2) := by
    rw [split, sub_add_eq_sub_sub]
    exact sub_mem hS2 (Ideal.sum_mem _ fun α hα => hS1 α (Finset.mem_sdiff.1 hα).2)
  have m2 : s' - ∑ α ∈ S ∪ S', t' α ∈ J ^ (N + 2) := by
    rw [Finset.union_comm, split, sub_add_eq_sub_sub]
    exact sub_mem hS2' (Ideal.sum_mem _ fun α hα => hS1' α (Finset.mem_sdiff.1 hα).2)
  have e : s' - c * T s = (s' - ∑ α ∈ S ∪ S', t' α) + c * T (-(s - ∑ α ∈ S ∪ S', t α)) := by
    simp only [ht, ← Finset.mul_sum, ← map_sum, map_neg, map_sub]
    ring
  rw [e]
  exact add_mem (Ideal.pow_le_pow_right (by omega) m2)
    (Ideal.mul_mem_left _ _ (hT N _ (neg_mem m1)))

end GlobalTheory.HeatValues

namespace GlobalTheory.HeatValues

theorem gs_id_eq {Ω : Type} [CommRing Ω] (z : Sp Ω) (a : Ω) :
    gs (𝟙 (Sp Ω)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom a) = toStkA z a := by
  rw [gs_eq (𝟙 (Sp Ω)) z ⊤ (show (𝟙 (Sp Ω) : Sp Ω ⟶ Sp Ω) z ∈ (⊤ : (Sp Ω).Opens) from trivial)]
  rfl

theorem cst_id {Ω : Type} [CommRing Ω] (z : Sp Ω) (a : Ω) : cst (𝟙 (Sp Ω)) z a = toStkA z a :=
  gs_id_eq z a

noncomputable def cstR {A : Type} [CommRing A] {Z : Scheme.{0}} (q : Z ⟶ Sp A) (z : Z) : A →+* Z.presheaf.stalk z where
  toFun a := cst q z a
  map_one' := by simp only [cst, map_one, gs_eq q z ⊤ (show q z ∈ (⊤ : (Sp A).Opens) from trivial)]
  map_mul' a b := by simp only [cst, map_mul, gs_mul q z ⊤ (show q z ∈ (⊤ : (Sp A).Opens) from trivial)]
  map_zero' := by simp only [cst, map_zero, gs_eq q z ⊤ (show q z ∈ (⊤ : (Sp A).Opens) from trivial)]
  map_add' a b := by simp only [cst, map_add, gs_add q z ⊤ (show q z ∈ (⊤ : (Sp A).Opens) from trivial)]

theorem cstR_id {Ω : Type} [CommRing Ω] (z : Sp Ω) (a : Ω) : cstR (𝟙 (Sp Ω)) z a = toStkA z a :=
  gs_id_eq z a

theorem sval_secAdd {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s t : (LB.LinComb L φ ε).Sec) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (DVR.SecOps.secAdd s t) r z J = sval s r z J + sval t r z J :=
  gs_add r z _ (hJ.mem φ r) _ _

theorem exists_integral {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : Unif I D A G) (k : ℕ) (hk : 1 ≤ k) (σ : H0 U.LG.L k) :
    ∃ (r₀ : R) (σ₀ : H0 U.LG.L k) (f₀ : ∀ α, D.toPre.SecB k α) (F : Fam D.toPre (FractionRing R) k),
      r₀ ≠ 0 ∧ DVR.SecIsMul G.hom r₀ σ₀ σ ∧ (∀ e, U.ExpandsAt e k σ₀ f₀) ∧
      ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (F.s α)
        (D.toPre.famφB α) (DegPre.famε k) (f₀ α) (DegPre.prB D.toPre (FractionRing R)).left
        (scal (DegPre.BF D.toPre (FractionRing R)).hom r₀) := by
  have := U.smooth
  have : Flat G.hom := inferInstance
  have hL := U.LG.isLB
  obtain ⟨s, hs⟩ := exists_sec hL (φ := fun _ : Fin 1 => pullback.fst G.hom (jK R) ≫ 𝟙 G.left)
    (ε := fun _ => (k : ℤ)) (φ' := fun _ : Fin 1 => pullback.fst G.hom (jK R)) (ε' := fun _ => (k : ℤ))
    (fun _ _ _ => by simp only [Category.comp_id])
    (DVR.pullSec U.LG.L _ _ σ (pullback.fst G.hom (jK R)))
  obtain ⟨F, ⟨r₀, hr₀, σ₀, f₀, h₁, hf₁, hE⟩, -⟩ := (U.expand k hk).1 s
  have hσs : GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ)) s
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (pullback.fst G.hom (jK R)) 1 :=
    DVR.SectionScalarValuation.secScal_of_sval hL fun y J hJ => by
      rw [hs _ _ y J hJ, DVR.SectionScalarValuation.sval_pullSec _ _ σ _ _ y hJ]
  exact ⟨r₀, σ₀, f₀, F, hr₀, GlobalTheory.ExpInt.secIsMul_of_generic G hL k σ σ₀ s r₀ hσs h₁, hE, hf₁⟩

theorem shiftEq_of_fam {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (k : ℕ)
    (F : Fam Q (FractionRing R) k) (f : ∀ α, Q.SecB k α) (r₀ : R)
    (hf : ∀ α, GeneratorPullback.SecScal Q.P.L (DegPre.famφ Q (FractionRing R) α) (DegPre.famε k) (F.s α)
      (Q.famφB α) (DegPre.famε k) (f α) (DegPre.prB Q (FractionRing R)).left
      (scal (DegPre.BF Q (FractionRing R)).hom r₀)) (mu α : Q.X) :
    ShiftEq Q k mu α (f α) (f (α + k • mu)) 0 (f (α + k • mu)) := by
  intro u hu hc z J hJ
  have fe := (secRel_iff Q.P.isLB _ _ _ _ _ _ _ _ _ u).1 (F.fe mu α u hu hc) _ (𝟙 _) z J hJ
  have a1 := GlobalTheory.IntegralExpansion.sval_of_secScal (hf (α + k • mu)) (𝟙 _) z hJ
  have a2 := GlobalTheory.IntegralExpansion.sval_of_secScal (hf α) (DegPre.trF Q (FractionRing R) mu).left z hJ
  have c1 : gs (DegPre.trF Q (FractionRing R) mu).left z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom r₀) =
      gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom r₀) := by
    rw [GlobalTheory.ExpInt.gs_scal, GlobalTheory.ExpInt.gs_scal, Over.w (DegPre.trF Q (FractionRing R) mu), Category.id_comp]
  have z0 : gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom (0 : R)) = 0 := by
    rw [GlobalTheory.ExpInt.gs_scal]; exact (cstR _ z).map_zero
  simp only [Category.id_comp] at a1 fe
  rw [z0, zero_mul, add_zero, a1, fe, Over.comp_left, a2, c1]
  ring

theorem exists_fam {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (k : ℕ) (f g : ∀ α, Q.SecB k α)
    (hf : ∀ mu α, ShiftEq Q k mu α (f α) (f (α + k • mu)) 0 (g (α + k • mu))) :
    ∃ F : Fam Q (FractionRing R) k, ∀ α, GeneratorPullback.SecScal Q.P.L (DegPre.famφ Q (FractionRing R) α) (DegPre.famε k)
      (F.s α) (Q.famφB α) (DegPre.famε k) (f α) (DegPre.prB Q (FractionRing R)).left 1 := by
  have hM := Q.P.isLB
  choose s hs using fun α => GlobalTheory.IndivisibleSection.exists_pull_val hM (f α) (DegPre.prB Q (FractionRing R)).left
    (φ' := DegPre.famφ Q (FractionRing R) α) (ε' := DegPre.famε k)
    (fun _ _ _ => Finset.prod_congr rfl fun i _ => by rw [DVR.GC.famφ_eq])
  refine ⟨⟨s, fun mu α u hu hc => (secRel_iff hM _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_⟩,
    fun α => DVR.SectionScalarValuation.secScal_of_sval hM fun y J hJ => (hs α _ (𝟙 _) y J hJ).symm⟩
  have e := hf mu α u hu hc y J hJ
  have z0 : gs (𝟙 _) y ⊤ (scal (DegPre.BF Q (FractionRing R)).hom (0 : R)) = 0 := by
    rw [GlobalTheory.ExpInt.gs_scal]; exact (cstR _ y).map_zero
  rw [hs _ _ (𝟙 _) y J hJ, hs _ _ _ y J hJ]
  simp only [Category.id_comp]
  rw [e, z0, zero_mul, add_zero, Over.comp_left]
  ring

end GlobalTheory.HeatValues

namespace GlobalTheory.HeatValues

theorem core {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (D : DegData R (maximalIdeal R))
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : Unif (maximalIdeal R) D A G) (NL : LB G.left) (hN : U.LG.L = NL)
    (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oD : D.toPre.OAct O) (Y : Ray oD)
    (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left)
    (hinv : ∀ a, IsInv Y.H (vH a) (dd a)) (Dr : Derivation ℤ R R)
    (h : Heat Y.H Y.q.left D.toPre.P.L dd ⇑Dr) (hbasic : IsBasic Y h) (hdef : HasDefect Y h (fun _ _ _ => 0))
    (i0 : h.J) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω)
    (x : Sp Ω ⟶ Y.H.left) (x' : Sp Ω ⟶ G.left) (δ : Fin n → Derivation ℤ Ω Ω)
    (hcompl : IsAdicComplete ((maximalIdeal R).map φ) Ω) (hx : x ≫ Y.H.hom = spMap φ)
    (hx' : x' ≫ G.hom = spMap φ) (hδφ : ∀ a r, δ a (φ r) = 0)
    (hδ : ∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f))
    (hpx : GlobalTheory.FormalPoint.IsPointOf U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx))
      (Over.homMk x' hx'))
    (dΩ : Derivation ℤ Ω Ω) (hW : ⊤ ≤ x ⁻¹ᵁ h.W i0)
    (hd : ∀ O f, O ≤ h.W i0 → ⊤ ≤ x ⁻¹ᵁ O → valR x O (h.d i0 O f) = dΩ (valR x O f))
    (g : GlobalTheory.RayEv.Transport.Frame NL (x' ≫ 𝟙 G.left)) (hg : g.IsGen) :
    ∃ (e : Ωˣ), ∀ (k : ℕ), 1 ≤ k → ∀ (σ : SecM (𝟙 G.left) NL k) (ω : Ω), IsValue (𝟙 _) NL x' g k σ ω →
      ∃ (r : R) (σ' : SecM (𝟙 G.left) NL k) (ω' : Ω), r ≠ 0 ∧ IsValue (𝟙 _) NL x' g k σ' ω' ∧
        ω' = φ r * ((e : Ω) ^ k * ringOp ⇑dΩ (fun a => ⇑(δ a)) (φ.mapMatrix h.Θ) (fun a => φ (h.u a))
          (valR x _ (h.p i0)) (valR x _ (h.p' i0)) k (((e⁻¹ : Ωˣ) : Ω) ^ k * ω)) := by
  subst hN
  haveI := hcompl
  have hL := U.LG.isLB
  have hM := D.toPre.P.isLB
  set ξ := Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx) with hξ
  have hlies : GlobalTheory.RayEv.Transport.Lies U.toUnifPre x' ξ.b.left := fun e Z r y hy => (hpx e Z r y hy).1
  obtain ⟨g', gM, hg', hgM, hfr⟩ :=
    GlobalTheory.TransportLimit.exists_frRel R (maximalIdeal R) D A G U.toUnifPre Ω φ x' hx' ξ.b.left hlies
  obtain ⟨ρ, hρ⟩ := GlobalTheory.FormalPoint.exists_ratio hL (φ := fun _ : PUnit => x') (ε := fun _ => 1)
    (φ' := fun _ : PUnit => x' ≫ 𝟙 G.left) (ε' := fun _ => 1) (fun _ _ _ => by simp only [Category.comp_id])
    g' g hg' hg
  have hxW : x (cpt Ω) ∈ h.W i0 := (top_le_iff_cpt x _).1 hW
  obtain ⟨JM, hJM, hJM0⟩ := exists_good D.toPre.P.L hM (cpt Ω) (fun _ : PUnit => x ≫ Y.q.left)
    (fun _ => h.j i0) (fun _ _ _ => rfl) (fun _ => h.le i0 hxW)
  obtain ⟨JL, hJL⟩ : ∃ JL, Good U.LG.L (cpt Ω) JL := by
    choose C hC using fun ψ : Sp Ω ⟶ G.left => exists_chart hL (ψ (cpt Ω))
    exact ⟨C, hC⟩
  have hbm : ⊤ ≤ (𝟙 (Sp Ω)) ⁻¹ᵁ LB.wchart D.toPre.P.L (fun _ : PUnit => ξ.b.left)
      (fun _ => JM (𝟙 _ ≫ ξ.b.left)) :=
    (top_le_iff_cpt _ _).2 (hJM.mem (fun _ : PUnit => ξ.b.left) (𝟙 _))
  have hu := toStkA_valR (𝟙 (Sp Ω)) _ (cpt Ω) hbm (gM.s fun _ => JM (𝟙 _ ≫ ξ.b.left))
  obtain ⟨uU, huU⟩ := GlobalTheory.FormalValue.isUnit_valR _ _ hbm (gM.s fun _ => JM (𝟙 _ ≫ ξ.b.left))
  have hκu : toStkA (cpt Ω) (uU : Ω) = (val gM (𝟙 _) (cpt Ω) JM).val := by rw [huU]; exact hu
  let ρU : Ωˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom.toMonoidHom ρ
  have hρc : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp Ω) (z : Z), (gm r z ⊤ ρ).val = cstR r z (ρU : Ω) := fun Z r z => by
    rw [← gs_unit r z ⊤ (show r z ∈ (⊤ : (Sp Ω).Opens) from trivial)]
    show _ = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ρ.val))
    rw [Iso.hom_inv_id_apply]
  refine ⟨ρU * uU⁻¹, fun k hk σ ω hσ => ?_⟩
  obtain ⟨r₀, σ₀, f₀, F, hr₀, hσ₀, hE₀, hF₀⟩ := exists_integral U k hk σ
  have hsh₀ := shiftEq_of_fam D.toPre k F f₀ r₀ hF₀
  choose f₁ hf₁ using fun α => GlobalTheory.T.torusInvariant_heatOperator_acts_on_fourierTerms R D O oD Y n vH dd hinv Dr h hbasic k α (f₀ α)
  have hsh₁ : ∀ mu α, ShiftEq D.toPre k mu α (f₁ α) (f₁ (α + k • mu)) 0 (f₀ (α + k • mu)) :=
    fun mu α => hdef k mu α (f₀ α) (f₁ α) (f₀ (α + k • mu)) (f₁ (α + k • mu)) hk (hsh₀ mu α) (hf₁ α)
      (hf₁ (α + k • mu))
  obtain ⟨F₁, hF₁⟩ := exists_fam D.toPre k f₁ f₀ hsh₁
  obtain ⟨s₁, ⟨r₁, hr₁, σ₁, f₂, -, hf₂, hE₁⟩, -⟩ := (U.expand k hk).2 F₁
  have hf₂₁ : ∀ α, DVR.SecIsMul D.toPre.P.A.hom r₁ (f₂ α) (f₁ α) := fun α =>
    GlobalTheory.IntegralExpansion.secIsMul_of_secScal hM _ (GlobalTheory.IntegralExpansion.prB_app_injective D.toPre) (hF₁ α)
      (by rw [Over.w (DegPre.prB D.toPre (FractionRing R))]; exact hf₂ α)
  obtain ⟨hdφ, hact⟩ := GlobalTheory.T.heatOperator_value_at_point_eq_ringOperator R Y.H D.toPre.P.A.left Y.q.left D.toPre.P.L n dd ⇑Dr h i0 Ω φ x hx δ hδ dΩ
    hW hd
  obtain ⟨s₀, t₀, hs₀, ht₀, had₀⟩ := GlobalTheory.RayEv.Transport.exists_adic_expansion R (maximalIdeal R) D A G
    U.toUnifPre Ω φ ξ (Over.homMk x' hx') hpx ξ.b.left rfl g' gM hg' hgM hfr k σ₀ f₀ hE₀
  obtain ⟨s₂, t₂, hs₂, ht₂, had₂⟩ := GlobalTheory.RayEv.Transport.exists_adic_expansion R (maximalIdeal R) D A G
    U.toUnifPre Ω φ ξ (Over.homMk x' hx') hpx ξ.b.left rfl g' gM hg' hgM hfr k σ₁ f₂ hE₁
  have j0le : h.W i0 ≤ LB.wchart D.toPre.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => h.j i0) :=
    fun y hy => Set.mem_iInter.2 fun _ => h.le i0 hy
  have termv : ∀ (α : D.toPre.X) (fα : D.toPre.SecB k α) (τ : SecM Y.q.left D.toPre.P.L k),
      IsTerm Y k α fα τ →
      toStkA (cpt Ω) (valR x (h.W i0) (rsT (τ.f fun _ => h.j i0) (h.W i0))) =
        sval fα (𝟙 (Sp Ω) ≫ ξ.b.left) (cpt Ω) JM * (val (ξ.s α) (𝟙 (Sp Ω)) (cpt Ω) JM).val := by
    intro α fα τ hτ
    have e1 := hτ (Over.mk (spMap φ)) (Over.homMk x hx) (cpt Ω) JM hJM
    have e2 : (Over.homMk x hx : Over.mk (spMap φ) ⟶ Y.H) ≫ Y.q = ξ.b := (Y.Φ_b _).symm
    rw [e2] at e1
    rw [← gs_id_eq, GlobalTheory.NormGen.gs_valR (𝟙 _) x _ hW, Category.id_comp]
    erw [GlobalTheory.KS.DlogPol.gs_rsT x (cpt Ω) j0le hxW]
    refine Eq.trans ?_ e1
    exact (sval_of τ x (cpt Ω) JM _ fun _ => hJM0 PUnit.unit).symm
  let RO : Ω → Ω := ringOp ⇑dΩ (fun a => ⇑(δ a)) (φ.mapMatrix h.Θ) (fun a => φ (h.u a))
    (valR x _ (h.p i0)) (valR x _ (h.p' i0)) k
  have huu : (uU : Ω) ^ k * ((uU⁻¹ : Ωˣ) : Ω) ^ k = 1 := by rw [← mul_pow, Units.mul_inv, one_pow]
  have hρρ : (ρU : Ω) ^ k * ((ρU⁻¹ : Ωˣ) : Ω) ^ k = 1 := by rw [← mul_pow, Units.mul_inv, one_pow]
  have key : ∀ α, t₂ α = (φ r₁ * ((uU⁻¹ : Ωˣ) : Ω) ^ k) * RO (t₀ α * (uU : Ω) ^ k) := by
    intro α
    obtain ⟨τ, τ', hτ, hτ', hact'⟩ := hf₁ α
    have a0 := termv α (f₀ α) τ hτ
    have a1 := termv α (f₁ α) τ' hτ'
    have b0 := ht₀ α _ (𝟙 (Sp Ω)) (cpt Ω) JM hJM
    have b2 := ht₂ α _ (𝟙 (Sp Ω)) (cpt Ω) JM hJM
    erw [gs_id_eq] at b0 b2
    have m2 := GlobalTheory.IndivisibleSection.sval_of_secIsMul (hf₂₁ α) (𝟙 (Sp Ω) ≫ ξ.b.left) (cpt Ω) hJM
    have cc : (𝟙 (Sp Ω) ≫ ξ.b.left) ≫ D.toPre.P.A.hom = 𝟙 (Sp Ω) ≫ spMap φ := by
      rw [Category.assoc, Over.w ξ.b]; rfl
    rw [cc, cst_comp, cst_id] at m2
    have v0 : valR x (h.W i0) (rsT (τ.f fun _ => h.j i0) (h.W i0)) = t₀ α * (uU : Ω) ^ k := by
      apply toStkA_injective
      rw [a0, b0, map_mul, map_pow, hκu, Units.val_pow_eq_pow_val]
    have v1 : φ r₁ * valR x (h.W i0) (rsT (τ'.f fun _ => h.j i0) (h.W i0)) = t₂ α * (uU : Ω) ^ k := by
      apply toStkA_injective
      rw [map_mul, a1, map_mul, map_pow, hκu, ← Units.val_pow_eq_pow_val, ← b2, m2, _root_.mul_assoc]
    rw [hact k τ τ' hact', v0] at v1
    linear_combination (-(((uU⁻¹ : Ωˣ) : Ω) ^ k)) * v1 - t₂ α * huu
  let T : Ω →+ Ω := AddMonoidHom.mk' (fun y => RO (y * (uU : Ω) ^ k)) (fun a b => by
    simp only [RO, add_mul]; exact ringOp_add _ _ _ _ _ _ _ _ _)
  have hT : ∀ N y, y ∈ ((maximalIdeal R).map φ) ^ (N + 2) → T y ∈ ((maximalIdeal R).map φ) ^ N :=
    fun N y hy => ringOp_mem _ dΩ δ _ _ _ _ k N _ (Ideal.mul_mem_right _ _ hy)
  have hs₂e : s₂ = (φ r₁ * ((uU⁻¹ : Ωˣ) : Ω) ^ k) * T s₀ :=
    eq_of_adic _ T hT _ s₀ s₂ t₀ t₂ key had₀ had₂
  have hTs : T s₀ = RO (s₀ * (uU : Ω) ^ k) := rfl
  have hs0rel : s₀ * (ρU : Ω) ^ k = φ r₀ * ω := by
    have a : sval σ₀ (𝟙 _ ≫ x') (cpt Ω) JL = _ := hs₀ _ (𝟙 _) (cpt Ω) JL hJL
    have b := GlobalTheory.IndivisibleSection.sval_of_secIsMul hσ₀ (𝟙 _ ≫ x') (cpt Ω) hJL
    have c := hσ _ (𝟙 _) (cpt Ω) JL hJL
    have d := hρ _ (𝟙 _) (cpt Ω) JL hJL
    have cc : (𝟙 (Sp Ω) ≫ x') ≫ G.hom = 𝟙 _ ≫ spMap φ := by rw [Category.assoc, hx']
    rw [cc, cst_comp, cst_id] at b
    erw [gs_id_eq] at a c
    have e := b.symm.trans a
    rw [c] at e
    erw [d] at e
    rw [mul_pow, Units.val_mul, Units.val_pow_eq_pow_val (gm _ _ _ ρ), hρc, cstR_id] at e
    apply toStkA_injective
    rw [map_mul, map_mul, map_pow]
    refine (Units.mul_left_inj (val g (𝟙 _) (cpt Ω) JL ^ k)).1 ?_
    linear_combination (-1 : (Sp Ω).presheaf.stalk (cpt Ω)) * e
  let c' : R := -(2 * (k : R) * r₁ * Dr r₀)
  refine ⟨r₁ * r₀, DVR.SecOps.secAdd σ₁ (DVR.SecOps.secScale (scal G.hom c') σ),
    s₂ * (ρU : Ω) ^ k + φ c' * ω, mul_ne_zero hr₁ hr₀, ?_, ?_⟩
  · intro Z r z J hJ
    have a : sval σ₁ (r ≫ x') z J = _ := hs₂ Z r z J hJ
    have c := hσ Z r z J hJ
    have d := hρ Z r z J hJ
    rw [sval_secAdd _ _ _ _ hJ, GlobalTheory.UU.ShiftExp.sval_secScale _ _ _ _ hJ, a, c]
    erw [d]
    rw [GlobalTheory.ExpInt.gs_scal,
      Category.assoc, hx', cst_comp, mul_pow, Units.val_mul, Units.val_pow_eq_pow_val (gm r z ⊤ ρ), hρc]
    change cstR r z s₂ * _ + cstR r z (φ c') * (cstR r z ω * _) = cstR r z _ * _
    rw [map_add, map_mul, map_mul, map_pow]
    ring
  · rw [hs₂e, hTs, show (ρU * uU⁻¹)⁻¹ = uU * ρU⁻¹ by rw [mul_inv_rev, inv_inv], Units.val_mul, Units.val_mul]
    have hX : s₀ * (uU : Ω) ^ k = φ r₀ * (((uU : Ω) * ((ρU⁻¹ : Ωˣ) : Ω)) ^ k * ω) := by
      linear_combination (((ρU⁻¹ : Ωˣ) : Ω) ^ k * (uU : Ω) ^ k) * hs0rel - s₀ * (uU : Ω) ^ k * hρρ
    rw [hX]
    simp only [RO]
    rw [ringOp_mul dΩ δ _ _ _ _ k (φ r₀) _ (fun a => hδφ a r₀), hdφ r₀]
    simp only [c', map_neg, map_mul, map_natCast, map_ofNat]
    linear_combination (2 * (k : Ω) * φ r₁ * φ (Dr r₀) * ω) *
      ((ρU : Ω) ^ k * ((ρU⁻¹ : Ωˣ) : Ω) ^ k * huu + hρρ)

end GlobalTheory.HeatValues

theorem GlobalTheory.HeatValues.heat_values_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D), IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∀ (i0 : h.J) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → ∀ (hx : x ≫ Y.H.hom = spMap φ) (hx' : x' ≫ t.G.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') → ∀ (dΩ : Derivation ℤ Ω Ω), ⊤ ≤ x ⁻¹ᵁ h.W i0 → (∀ O f, O ≤ h.W i0 → ⊤ ≤ x ⁻¹ᵁ O → valR x O (h.d i0 O f) = dΩ (valR x O f)) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∃ (e : Ωˣ) (p0 p0' : Ω), ∀ (k : ℕ), 1 ≤ k → ∀ (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), IsValue (𝟙 _) t.PP.L x' g k σ ω → ∃ (r : R) (σ' : SecM (𝟙 t.G.left) t.PP.L k) (ω' : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ' ω' ∧ ω' = φ r * ((e : Ω) ^ k * ringOp ⇑dΩ (fun a => ⇑(δ a)) (φ.mapMatrix h.Θ) (fun a => φ (h.u a)) p0 p0' k (((e⁻¹ : Ωˣ) : Ω) ^ k * ω)) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam _ _ _ Y n vH dd hinv v' _ D h hbasic hdef i0 Ω _ _ _ φ x x' δ hcompl
    hx hx' hδφ hδ hpx dΩ hW hd g hg
  letI := H.starRing
  obtain ⟨e, he⟩ := GlobalTheory.HeatValues.core P.D P.U t.PP.L (congrArg (fun q => q.L) P.bundle) (𝓞 E) P.oD Y n vH dd hinv
    D h hbasic hdef i0 Ω φ x x' δ hcompl hx hx' hδφ hδ hpx dΩ hW hd g hg
  exact ⟨e, _, _, he⟩
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heat_operator_values_of_sections_complete_local_ring : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D), IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∀ (i0 : h.J) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → ∀ (hx : x ≫ Y.H.hom = spMap φ) (hx' : x' ≫ t.G.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') → ∀ (dΩ : Derivation ℤ Ω Ω), ⊤ ≤ x ⁻¹ᵁ h.W i0 → (∀ O f, O ≤ h.W i0 → ⊤ ≤ x ⁻¹ᵁ O → valR x O (h.d i0 O f) = dΩ (valR x O f)) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∃ (e : Ωˣ) (p0 p0' : Ω), ∀ (k : ℕ), 1 ≤ k → ∀ (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), IsValue (𝟙 _) t.PP.L x' g k σ ω → ∃ (r : R) (σ' : SecM (𝟙 t.G.left) t.PP.L k) (ω' : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ' ω' ∧ ω' = φ r * ((e : Ω) ^ k * ringOp ⇑dΩ (fun a => ⇑(δ a)) (φ.mapMatrix h.Θ) (fun a => φ (h.u a)) p0 p0' k (((e⁻¹ : Ωˣ) : Ω) ^ k * ω)) := by
  atlas_forward_decl GlobalTheory.HeatValues.heat_values_at_point
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat

theorem ringOp_map_of_intertwine {A B : Type} [CommRing A] [CommRing B] (iK : A →+* B) {n : ℕ} (d : A → A) (dd : Fin n → A → A)
    (d' : B → B) (dd' : Fin n → B → B) (hd : ∀ w, d' (iK w) = iK (d w)) (hdd : ∀ a w, dd' a (iK w) = iK (dd a w))
    (Θ : Matrix (Fin n) (Fin n) A) (u : Fin n → A) (p p' : A) (k : ℕ) (f : A) :
    iK (ringOp d dd Θ u p p' k f) = ringOp d' dd' (iK.mapMatrix Θ) (fun a => iK (u a)) (iK p) (iK p') k (iK f) := by
  simp only [ringOp, map_sub, map_add, map_mul, map_sum, map_pow, map_natCast, map_ofNat, hd, hdd,
    RingHom.mapMatrix_apply, Matrix.map_apply]

theorem ringOp_mul_of_const {K : Type} [CommRing K] {n : ℕ} (d : K → K) (δ : Fin n → K → K)
    (Θ : Matrix (Fin n) (Fin n) K) (u : Fin n → K) (p p' : K) (k : ℕ) (c s : K)
    (hd : d (c * s) = c * d s + s * d c) (h1 : ∀ a y, δ a (c * y) = c * δ a y) :
    ringOp d δ Θ u p p' k (c * s) = c * ringOp d δ Θ u p p' k s + 2 * (k : K) * d c * s := by
  simp only [ringOp, h1, hd, mul_left_comm _ c, ← Finset.mul_sum]
  try ring

theorem exists_derivation_fractionRing_ext (Ω : Type) [CommRing Ω] [IsDomain Ω] (d : Derivation ℤ Ω Ω) :
    ∃ dL : Derivation ℤ (FractionRing Ω) (FractionRing Ω),
      ∀ w, dL (algebraMap Ω (FractionRing Ω) w) = algebraMap Ω (FractionRing Ω) (d w) := by
  obtain ⟨δ', hder, hδ'⟩ := Formalism.L2.Pj.GenericSectionMinimum.IsDer.ofLoc (nonZeroDivisors Ω) (B := FractionRing Ω)
    (fun w => algebraMap Ω (FractionRing Ω) (d w)) (fun a b => by simp)
    (fun a b => by simp [Derivation.leibniz, smul_eq_mul])
  have hsm : ∀ (z : ℤ) (a : FractionRing Ω), δ' (z • a) = z • δ' a := by
    intro z a
    induction z using Int.induction_on with
    | zero => simp [hder.der_zero]
    | succ i ih => simp only [add_smul, one_smul, hder.add, ih]
    | pred i ih => simp only [sub_smul, one_smul, hder.der_sub, ih]
  have hint : ∀ m : ℤ, δ' (m : FractionRing Ω) = 0 := fun m => by
    have := hsm m 1
    rw [zsmul_eq_mul, _root_.mul_one, hder.der_one] at this
    simpa using this
  have hlb : ∀ a b : FractionRing Ω, δ' (a * b) = a • δ' b + b • δ' a := fun a b => by
    rw [hder.mul, smul_eq_mul, smul_eq_mul]
  let dL : Derivation ℤ (FractionRing Ω) (FractionRing Ω) := { toFun := δ', map_add' := hder.add, map_smul' := fun m y => by rw [RingHom.id_apply, Algebra.smul_def, eq_intCast, zsmul_eq_mul, hder.mul, hint m, MulZeroClass.mul_zero, add_zero], map_one_eq_zero' := hder.der_one, leibniz' := hlb }
  exact ⟨dL, hδ'⟩

theorem heat_acts_on_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D), IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∀ (i0 : h.J) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → ∀ (hx : x ≫ Y.H.hom = spMap φ) (hx' : x' ≫ t.G.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') → ∀ (dΩ : Derivation ℤ Ω Ω), ⊤ ≤ x ⁻¹ᵁ h.W i0 → (∀ O f, O ≤ h.W i0 → ⊤ ≤ x ⁻¹ᵁ O → valR x O (h.d i0 O f) = dΩ (valR x O f)) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∃ (dt : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u' : Fin n → (FractionRing Ω)) (p p' : (FractionRing Ω)), (∀ r, dt ((algebraMap Ω (FractionRing Ω)) (φ r)) = (algebraMap Ω (FractionRing Ω)) (φ (D r))) ∧ ∀ (k : ℕ), 1 ≤ k → ∀ s : (FractionRing Ω), (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (s)) → (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (ringOp ⇑dt (fun a => ⇑(δL a)) (((algebraMap Ω (FractionRing Ω)).comp φ).mapMatrix h.Θ) u' p p' k s)) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam hmono htt hab
  intro Y n vH dd hinv v' hpt D h hbasic hdef i0 Ω _ _ _ φ x x' δ hcompl hx hx' hδφ hδ hpx dΩ hW hdΩ g hg δL hδL
  letI := H.starRing
  have hDφ := (GlobalTheory.T.heatOperator_value_at_point_eq_ringOperator R Y.H _ _ P.D.toPre.P.L n dd ⇑D h i0 Ω φ x hx δ hδ dΩ hW hdΩ).1
  obtain ⟨e, p0, p0', hcore⟩ := GlobalTheory.T.heat_operator_values_of_sections_complete_local_ring E H R t P m tt gam hmono htt hab Y n vH dd hinv v' hpt D h hbasic hdef i0 Ω φ x x' δ
    hcompl hx hx' hδφ hδ hpx dΩ hW hdΩ g hg
  obtain ⟨dL, hdL⟩ := exists_derivation_fractionRing_ext Ω dΩ
  set iK := algebraMap Ω (FractionRing Ω) with hiK
  have hiKinj : Function.Injective iK := IsFractionRing.injective Ω (FractionRing Ω)
  have h2R : IsUnit (2 : R) := by
    have := (isUnit_iff_ne_zero.2 (two_ne_zero : (2 : ℚ) ≠ 0)).map (algebraMap ℚ R)
    rwa [map_ofNat] at this
  have h2K : (2 : FractionRing Ω) ≠ 0 := by
    have := (h2R.map (iK.comp φ)).ne_zero
    rwa [map_ofNat] at this
  have hsymm : ((iK.comp φ).mapMatrix h.Θ)ᵀ = (iK.comp φ).mapMatrix h.Θ := by
    show (h.Θ.map _)ᵀ = h.Θ.map _
    rw [← Matrix.transpose_map, h.symm]
  have hce : iK ((e⁻¹ : Ωˣ) : Ω) ≠ 0 := fun h0 => (e⁻¹).ne_zero (hiKinj (h0.trans (map_zero iK).symm))
  obtain ⟨d', u'', q, q', hd'c, hconj⟩ := GlobalTheory.T.heatOperatorOnRing_conj_pow_fractionField Ω n dL δL ((iK.comp φ).mapMatrix h.Θ) hsymm h2K
    (fun a => iK (φ (h.u a))) (iK p0) (iK p0') _ hce
  refine ⟨d', u'', q, q', fun r => ?_, ?_⟩
  · rw [hd'c _ (fun a => by rw [hδL, hδφ, map_zero]), hdL, hDφ]
  intro k hk s ⟨r₁, σ, ω, hr₁, hv, hs⟩
  obtain ⟨r₂, σ₂, ω₂, hr₂, hv₂, hω₂⟩ := hcore k hk σ ω hv
  have key : iK ω₂ = iK (φ r₂) * ringOp ⇑d' (fun a => ⇑(δL a)) ((iK.comp φ).mapMatrix h.Θ) u'' q q' k (iK ω) := by
    rw [hω₂, map_mul, map_mul, map_pow, ringOp_map_of_intertwine iK _ _ _ _ hdL hδL, map_mul, map_pow]
    have e1 : iK.mapMatrix (φ.mapMatrix h.Θ) = (iK.comp φ).mapMatrix h.Θ := by
      ext a b; simp
    rw [e1, hconj, ← _root_.mul_assoc (iK (e : Ω) ^ k), ← mul_pow, ← map_mul, Units.mul_inv, map_one, one_pow, _root_.one_mul]
  by_cases hc1 : φ r₁ = 0
  · exact ⟨r₁, σ, ω, hr₁, hv, by rw [hs, hc1]; simp⟩
  · have hδc : ∀ a, δL a (iK (φ r₁)) = 0 := fun a => by rw [hδL, hδφ, map_zero]
    have hdc : d' (iK (φ r₁)) = iK (φ (D r₁)) := by rw [hd'c _ hδc, hdL, hDφ]
    have hs' : iK ω = iK (φ r₁) * s := hs
    have hRO := ringOp_mul_of_const ⇑d' (fun a => ⇑(δL a)) ((iK.comp φ).mapMatrix h.Θ) u'' q q' k (iK (φ r₁)) s
      (by rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]) (fun a y => by
        rw [Derivation.leibniz, hδc, smul_zero, add_zero, smul_eq_mul])
    rw [← hs', hdc] at hRO
    obtain ⟨σ₃, hv₃⟩ := GlobalTheory.T.sectionValueInFrame_linearCombination R t.G t.PP.L Ω φ x' hx' g k σ₂ σ ω₂ ω r₁ (-(2 * (k : R)) * D r₁ * r₂) hv₂ hv
    refine ⟨r₁ * r₁ * r₂, σ₃, _, mul_ne_zero (mul_ne_zero hr₁ hr₁) hr₂, hv₃, ?_⟩
    simp only [RingHom.comp_apply, map_add, map_mul, map_neg, map_natCast, map_ofNat]
    rw [key, hRO, hs']
    ring

end GlobalTheory.Heat
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commuting_heatOperators_act_on_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D), IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∀ (i0 : h.J) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → ∀ (hx : x ≫ Y.H.hom = spMap φ) (hx' : x' ≫ t.G.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') → ∀ (dΩ : Derivation ℤ Ω Ω), ⊤ ≤ x ⁻¹ᵁ h.W i0 → (∀ O f, O ≤ h.W i0 → ⊤ ≤ x ⁻¹ᵁ O → valR x O (h.d i0 O f) = dΩ (valR x O f)) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∃ (dt : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u' : Fin n → (FractionRing Ω)) (p p' : (FractionRing Ω)), (∀ r, dt ((algebraMap Ω (FractionRing Ω)) (φ r)) = (algebraMap Ω (FractionRing Ω)) (φ (D r))) ∧ ∀ (k : ℕ), 1 ≤ k → ∀ s : (FractionRing Ω), (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (s)) → (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (ringOp ⇑dt (fun a => ⇑(δL a)) (((algebraMap Ω (FractionRing Ω)).comp φ).mapMatrix h.Θ) u' p p' k s)) := by
  atlas_forward_decl GlobalTheory.Heat.heat_acts_on_values
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.KSChartRes

theorem isUnit_of_comap_mem {A S : Type} [CommRing A] [CommRing S] (φ : A →+* S) (s : A)
    (h : ∀ x : PrimeSpectrum S, PrimeSpectrum.comap φ x ∈ PrimeSpectrum.basicOpen s) : IsUnit (φ s) := by
  by_contra hn
  obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ (Ideal.span_singleton_ne_top hn)
  exact h ⟨m, hm.isPrime⟩ (hsm (Ideal.mem_span_singleton_self _))

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    spMap β ≫ spMap α = spMap (β.comp α) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem dualMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (α : A →+* B) (β : B →+* C) :
    (dualMap β).comp (dualMap α) = dualMap (β.comp α) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap]

theorem isKS_top_of_basicOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (m : ℕ) (tt : Fin m → R) (n : ℕ) (v' : Fin n → TanM (𝟙 (Sp R)) t.G) (D : Derivation ℤ R R) (DV : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)) (Θ : Matrix (Fin n) (Fin n) R), (∀ r, DV (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D r))) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (fun a => spMap (dualMap (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) ≫ (tv (v' a)).left) ⇑DV ((((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).mapMatrix Θ) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) (fun a => spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) ≫ (tv (v' a)).left) (fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r))) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.mapMatrix Θ) := by
  intro E _ _ _ H R _ _ _ _ _ _ t m tt n v' D DV Θ hD ⟨J, Wc, j, d, hsup, hj, hfld, hcomp, htest⟩
  set s := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i) with hs
  set Wa := (Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) s with hWa
  have hWV : ∀ i, Wc i ≤ t.G.hom ⁻¹ᵁ Wa.1 := fun i =>
    (le_iSup Wc i).trans (hsup.le.trans (t.G.hom.preimage_mono inf_le_left))
  have hle : Wa.1 ≤ ⊤ := le_top
  refine ⟨J, Wc, j, d, ?_, hj, hfld, fun i h r => ?_, fun i i' O hO f S _ φ g₀ w hg₀ hO' hw => ?_⟩
  · rw [hsup, top_inf_eq]
    exact congrArg _ (inf_idem _)
  · have e : ∀ x, (t.G.hom.appLE ⊤ (Wc i) h).hom x =
        (t.G.hom.appLE Wa.1 (Wc i) (hWV i)).hom (((Sp R).presheaf.map (homOfLE hle).op).hom x) := fun x =>
      (congrArg (fun k => k.hom x) (t.G.hom.map_appLE (hWV i) (homOfLE hle).op)).symm
    have hr : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) = r :=
      Iso.hom_inv_id_apply _ _
    rw [e, e, hcomp i (hWV i)]
    have := hD ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r)
    rw [hr] at this
    exact congrArg _ this
  · have hOW : O ≤ t.G.hom ⁻¹ᵁ (Wa.1 ⊓ (Sp R).basicOpen s) :=
      hO.trans (inf_le_left.trans ((le_iSup Wc i).trans hsup.le))
    have hu : IsUnit (φ s) := by
      refine isUnit_of_comap_mem φ s fun x => ?_
      have hx : g₀ x ∈ O := hO' (show x ∈ (⊤ : (Sp S).Opens) from trivial)
      have hV : t.G.hom (g₀ x) ∈ (Sp R).basicOpen s := (hOW hx).2
      have e1 : t.G.hom (g₀ x) = (g₀ ≫ t.G.hom) x := rfl
      rw [e1, hg₀] at hV
      have h2 : (spMap φ) x ∈ (GlobalTheory.LogKS.chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ⁻¹ᵁ (Sp R).basicOpen s := hV
      change (spMap φ) x ∈ (isAffineOpen_top (Sp R)).fromSpec ⁻¹ᵁ (Sp R).basicOpen s at h2
      rw [(isAffineOpen_top (Sp R)).fromSpec_preimage_basicOpen s] at h2
      exact h2
    letI : Algebra Γ(Sp R, ⊤) Γ(Sp R, Wa.1) := ((Sp R).presheaf.map (homOfLE hle).op).hom.toAlgebra
    have hl : IsLocalization.Away s Γ(Sp R, Wa.1) :=
      (isAffineOpen_top (Sp R)).isLocalization_of_eq_basicOpen s (homOfLE hle) rfl
    obtain ⟨ψ, hψ⟩ : ∃ ψ : Γ(Sp R, Wa.1) →+* S, ψ.comp ((Sp R).presheaf.map (homOfLE hle).op).hom = φ :=
      ⟨IsLocalization.Away.lift s hu, IsLocalization.lift_comp _⟩
    subst hψ
    have hres : spMap ((Sp R).presheaf.map (homOfLE hle).op).hom ≫
        GlobalTheory.LogKS.chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) = GlobalTheory.LogKS.chart Wa :=
      (isAffineOpen_top (Sp R)).map_fromSpec Wa.2 (homOfLE hle).op
    have := htest i i' O hO f S ψ g₀ w ?_ hO' ?_
    · exact this
    · rw [hg₀, ← hres, ← Category.assoc, spMap_comp']
    · intro a
      obtain ⟨g', v'', h₁, h₂, h₃⟩ := hw a
      refine ⟨g', v'', h₁, ?_, h₃⟩
      rw [h₂]
      dsimp only
      rw [← Category.assoc, ← Category.assoc, spMap_comp']
      erw [spMap_comp']
      erw [dualMap_comp']

end GlobalTheory.KSChartRes
end
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isKodairaSpencer_affineChart_of_basicOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (m : ℕ) (tt : Fin m → R) (n : ℕ) (v' : Fin n → TanM (𝟙 (Sp R)) t.G) (D : Derivation ℤ R R) (DV : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)) (Θ : Matrix (Fin n) (Fin n) R), (∀ r, DV (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D r))) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (fun a => spMap (dualMap (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) ≫ (tv (v' a)).left) ⇑DV ((((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).mapMatrix Θ) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) (fun a => spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) ≫ (tv (v' a)).left) (fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r))) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.mapMatrix Θ) := by
  atlas_forward_decl GlobalTheory.KSChartRes.isKS_top_of_basicOpen
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TanRayBasis

theorem vBasis_of_isPointOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∃ b : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G), ⇑b = v' := by
  intro E _ _ _ H R _ _ _ _ _ _ t P
  letI := H.starRing
  intro Y n vH v' hv
  obtain ⟨b, hb⟩ := GlobalTheory.TanRay.tanBasis_of_isPointOf E H R t P Y n vH v' hv
  exact ⟨b, funext hb⟩

end GlobalTheory.TanRayBasis
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentBasis_uniformisedGroup_of_raynaudExtension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∃ b : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G), ⇑b = v' := by
  atlas_forward_decl GlobalTheory.TanRayBasis.vBasis_of_isPointOf
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.RayInt

open ReciprocityTheory.ChartRestriction.G.Semi TopologicalSpace

attribute [local instance] SplitExt.free SplitExt.finite

theorem mem_chart_of_mem {S : Scheme.{0}} (E : SplitExt S) (j : E.ChartIdx) (b : E.B.left)
    (h : ∀ k, b ∈ (E.O (E.basis k)).L.U (j k)) : b ∈ E.chart j := by
  have e : E.chart j = Finset.univ.inf (fun k => (E.O (E.basis k)).L.U (j k)) :=
    (Finset.inf_univ_eq_iInf _).symm
  rw [e, ← SetLike.mem_coe, Opens.coe_finset_inf]
  simp only [Finset.inf_eq_iInf, Finset.mem_univ, iInf_true, Set.iInf_eq_iInter, Set.mem_iInter,
    Function.comp_apply, SetLike.mem_coe]
  exact h

theorem isIntegral_of_isGt (R : Type) [CommRing R] [IsDomain R] (E : SplitExt (Spec (CommRingCat.of R)))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (hG : E.IsGt G) (hs : Smooth G.hom) :
    IsIntegral G.left := by
  obtain ⟨d⟩ := hG
  have hB := E.isAbelian
  haveI : Smooth E.B.hom := hB.smooth
  haveI : GeometricallyConnected E.B.hom := hB.geomConnected
  have hSne : Nonempty (Spec (CommRingCat.of R)) := inferInstance
  have hBne : Nonempty E.B.left := ⟨(η[E.B] : 𝟙_ _ ⟶ E.B).left (show (𝟙_ (Over _)).left from hSne.some)⟩
  haveI : IrreducibleSpace E.B.left :=
    GlobalTheory.irreducibleSpace_of_smooth_of_geometricallyConnected_domain R E.B ‹_› ‹_› hBne
  haveI : IsReduced E.B.left := GlobalTheory.isReduced_of_smooth_of_isReduced E.B.hom
  haveI : IsIntegral E.B.left := isIntegral_of_irreducibleSpace_of_isReduced _
  haveI : IsReduced G.left := GlobalTheory.isReduced_of_smooth_of_isReduced G.hom
  obtain ⟨b⟩ := hBne
  have hk : ∀ k, ∃ i, b ∈ (E.O (E.basis k)).L.U i := fun k => by
    have hb : b ∈ (⊤ : E.B.left.Opens) := trivial
    rw [← (E.O (E.basis k)).isLB.cover, Opens.mem_iSup] at hb
    exact hb
  choose j hj using hk
  have hbj : b ∈ E.chart j := mem_chart_of_mem E j b hj
  obtain ⟨V, hV, hbV, hVj⟩ := (Opens.isBasis_iff_nbhd.mp E.B.left.isBasis_affineOpens) hbj
  have hbV' : b ∈ V := hbV
  haveI : Nonempty V := ⟨⟨b, hbV'⟩⟩
  haveI := d.q_affine
  haveI := d.q_flat
  have hsurj := d.q_surjective
  set W : G.left.Opens := d.q.left ⁻¹ᵁ V with hWdef
  have hV : IsAffineOpen V := hV
  have hW : IsAffineOpen W := hV.preimage d.q.left
  have hbij := d.coord j V hV hVj
  haveI : IsDomain Γ(G.left, W) :=
    Function.Injective.isDomain (RingEquiv.ofBijective _ hbij).symm.toRingHom
      (RingEquiv.ofBijective _ hbij).symm.injective
  obtain ⟨g, hg⟩ := hsurj.surj b
  have hgW : g ∈ W := by show d.q.left g ∈ V; rw [hg]; exact hbV'
  haveI : Nonempty W := ⟨⟨g, hgW⟩⟩
  haveI : IsAffine W := hW
  haveI : IsDomain Γ(W, ⊤) :=
    Function.Injective.isDomain (W.topIso).commRingCatIsoToRingEquiv.toRingHom
      (W.topIso).commRingCatIsoToRingEquiv.injective
  haveI : IsIntegral W := isIntegral_of_isAffine_of_isDomain W
  have hirrW : IsIrreducible (W : Set G.left) := by
    have hI := (IrreducibleSpace.isIrreducible_univ W).image (⇑W.ι) (Scheme.Hom.continuous _).continuousOn
    rwa [Set.image_univ, Scheme.Opens.range_ι] at hI
  have hη : genericPoint E.B.left ∈ V :=
    ((genericPoint_spec E.B.left).mem_open_set_iff V.isOpen).2 ⟨b, trivial, hbV'⟩
  have hcl : closure (W : Set G.left) = Set.univ := by
    refine Set.eq_univ_of_forall fun z => ?_
    obtain ⟨z', hz', e⟩ := Flat.generalizingMap d.q.left (genericPoint_specializes (d.q.left z))
    have hz'W : z' ∈ (W : Set G.left) := by show d.q.left z' ∈ V; rw [e]; exact hη
    exact closure_mono (Set.singleton_subset_iff.2 hz'W) (specializes_iff_mem_closure.mp hz')
  haveI : IrreducibleSpace G.left := by
    rw [irreducibleSpace_def]
    have := hirrW.closure
    rwa [hcl] at this
  exact isIntegral_of_irreducibleSpace_of_isReduced _

theorem isIntegral_H : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa), IsIntegral Y.H.left := by
  intro R _ _ _ _ Q O _ _ _ oa Y
  exact isIntegral_of_isGt R _ Y.H Y.isGt (GlobalTheory.RayTan.smooth_H R Q O oa Y)

end GlobalTheory.RayInt
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_raynaudExtension_noetherian_local : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa), IsIntegral Y.H.left := by
  atlas_forward_decl GlobalTheory.RayInt.isIntegral_H
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kodairaSpencer_abelianLocus_chartRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (D : Derivation ℤ R R), ∀ (DV : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)), ∃ Θ₁, IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (fun a => spMap (dualMap (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) ≫ (tv (v' a)).left) ⇑DV Θ₁ := by
  first | exact @GlobalTheory.KSAbLocus.exists_isKS_abLocus | exact GlobalTheory.KSAbLocus.exists_isKS_abLocus | (intros; apply GlobalTheory.KSAbLocus.exists_isKS_abLocus <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSAbLocusSymm

theorem tanBasis_of_basis' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R]
    (t : SAB H (Sp R)) {n : ℕ} (b : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) {T : Type} [CommRing T]
    (φ : R →+* T) :
    (∀ i, IsTanAtG t (spMap φ ≫ 𝟙 (Sp R)) (spMap (dualMap φ) ≫ (tv (b i)).left)) ∧
      ∀ w, IsTanAtG t (spMap φ ≫ 𝟙 (Sp R)) w →
        ∃! a : Fin n → T, IsCombAtG t (spMap φ ≫ 𝟙 (Sp R)) (fun i => spMap (dualMap φ) ≫ (tv (b i)).left) a w := by
  refine GlobalTheory.LocM.FrameBase.tanBasis_baseChange t φ (𝟙 (Sp R)) n _ (fun i => GlobalTheory.LieMet.isTan_tv (b i)) ?_
  intro w hw
  refine ⟨b.repr (GlobalTheory.LieMet.tanOf hw), ?_, fun a ha => ?_⟩
  · show IsCombAtG t _ _ _ (tv (GlobalTheory.LieMet.tanOf hw)).left
    rw [GlobalTheory.LieMet.isComb_iff]
    exact (b.sum_repr _).symm
  · have h := (GlobalTheory.LieMet.isComb_iff b a (GlobalTheory.LieMet.tanOf hw)).1 ha
    rw [h]
    ext i
    simp [Finsupp.single_apply]

theorem exists_symm_isKS_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (DV : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)), ∃ Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1), Θ₁ᵀ = Θ₁ ∧ IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (fun a => spMap (dualMap (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) ≫ (tv (v' a)).left) ⇑DV Θ₁ := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam hmon htt hab n v' DV
  obtain ⟨Θ₁, hKS⟩ := GlobalTheory.T.exists_kodairaSpencer_abelianLocus_chartRing E H R t P m tt gam hmon htt hab n v' 0 DV
  refine ⟨Θ₁, ?_, hKS⟩
  let U : (Sp R).affineOpens := (Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens))
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))
  let ρ : R →+* Γ(Sp R, U.1) := ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤)
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have hc : spMap ρ ≫ 𝟙 (Sp R) = chart U := by
    rw [Category.comp_id]
    show Spec.map _ = U.2.fromSpec
    rw [← (isAffineOpen_top (Sp R)).map_fromSpec U.2 (homOfLE ((Sp R).basicOpen_le (U := ⊤)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec]
    rw [show CommRingCat.ofHom ρ = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op from rfl]
    erw [Spec.map_comp]
    rfl
  obtain ⟨hv, hb⟩ := tanBasis_of_basis' t v' ρ
  rw [hc] at hv hb
  have h2 : (U.1 : (Sp R).Opens) = PrimeSpectrum.basicOpen (∏ i, tt i) :=
    basicOpen_eq_of_affine (R := CommRingCat.of R) (∏ i, tt i)
  have h4 : ∀ q : Sp R, q ∈ ((U.1 : (Sp R).Opens) : Set (Sp R)) → ∏ i, tt i ∉ q.asIdeal := by
    intro q hq
    rw [h2] at hq
    exact hq
  have hx : ∀ s, ∏ i, tt i ∉ ((chart U) s).asIdeal := fun s =>
    h4 _ (by rw [← U.2.range_fromSpec]; exact ⟨s, rfl⟩)
  have hne : ∏ i, tt i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => htt i
  haveI : Nonempty (U.1 : (Sp R).Opens) := by
    refine ⟨⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R), ?_⟩⟩
    show _ ∈ ((U.1 : (Sp R).Opens) : Set (Sp R))
    rw [h2]
    show ∏ i, tt i ∉ (⊥ : Ideal R)
    simpa using hne
  haveI : IsDomain Γ(Sp R, U.1) := inferInstance
  let K := FractionRing Γ(Sp R, U.1)
  let x₀ : Γ(Sp R, U.1) →+* K := algebraMap _ _
  letI : Algebra ℚ K := ((x₀.comp ρ).comp (algebraMap ℚ R)).toAlgebra
  haveI : CharZero K := algebraRat.charZero K
  obtain ⟨PP', cub, sym, adj, prim, mm, -⟩ := sabPull proved_CubePullSt (spMap x₀ ≫ chart U) t
  have hx' : ∀ s, ∏ i, tt i ∉ ((spMap x₀ ≫ chart U) s).asIdeal := fun s => hx ((spMap x₀) s)
  obtain ⟨hP, hA, hK⟩ := GlobalTheory.AbLocusPol.isProper_relAmple_kTriv_of_abLocus E H R t P m tt htt hab _
    (spMap x₀ ≫ chart U) _ hx' ⟨mm⟩
  obtain ⟨P₀, e, he⟩ := GlobalTheory.PolDvr.exists_polAV _ hP hA hK
  obtain ⟨w, g, -⟩ := mm.lin
  obtain ⟨h1, h2'⟩ := he t.G (spMap x₀ ≫ chart U) mm.φ t.PP.L mm.cart ⟨w, g⟩
  have hsym := GlobalTheory.FibSym.map_transpose_eq E H (Sp R) t _ U n _ hv hb K x₀ P₀ _ h1 h2' le_rfl _ Θ₁ hKS
  ext i j
  have hij := congrFun (congrFun hsym i) j
  simp only [Matrix.transpose_apply, Matrix.map_apply] at hij
  exact IsFractionRing.injective Γ(Sp R, U.1) K hij

end GlobalTheory.KSAbLocusSymm
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_kodairaSpencer_abelianLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (DV : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)), ∃ Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1), Θ₁ᵀ = Θ₁ ∧ IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (fun a => spMap (dualMap (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) ≫ (tv (v' a)).left) ⇑DV Θ₁ := by
  atlas_forward_decl GlobalTheory.KSAbLocusSymm.exists_symm_isKS_abLocus
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KBracket

theorem exists_der_ext {A S : Type} [CommRing A] [CommRing S] [Algebra A S] (M : Submonoid A) [IsLocalization M S]
    (δ : Derivation ℤ A A) : ∃ δS : Derivation ℤ S S, ∀ a, δS (algebraMap A S a) = algebraMap A S (δ a) := by
  let h : A →+* DualNumber S :=
    { toFun := fun a => TrivSqZeroExt.inl (algebraMap A S a) + TrivSqZeroExt.inr (algebraMap A S (δ a))
      map_one' := by ext <;> simp [-DualNumber.inr_eq_smul_eps]
      map_mul' := fun a b => by ext <;> simp [Derivation.leibniz, Algebra.smul_def, mul_comm, add_comm, -DualNumber.inr_eq_smul_eps]
      map_zero' := by ext <;> simp [-DualNumber.inr_eq_smul_eps]
      map_add' := fun a b => by ext <;> simp [add_add_add_comm, -DualNumber.inr_eq_smul_eps] }
  have hu : ∀ m : M, IsUnit (h m) := fun m => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by
    simpa [h] using IsLocalization.map_units S m)
  let L : S →+* DualNumber S := IsLocalization.lift hu
  have hfst : ∀ x, (L x).fst = x := by
    have : (TrivSqZeroExt.fstHom S S S).toRingHom.comp L = RingHom.id S := by
      refine IsLocalization.ringHom_ext M (RingHom.ext fun a => ?_)
      simp [L, h, -DualNumber.inr_eq_smul_eps]
    exact fun x => congr($this x)
  let δS : Derivation ℤ S S := Derivation.mk'
    ((show S →+ S from
      { toFun := fun x => (L x).snd, map_zero' := by simp, map_add' := fun x y => by simp }).toIntLinearMap)
    (fun x y => by
      show (L (x * y)).snd = x • (L y).snd + y • (L x).snd
      rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst]
      simp [mul_comm])
  refine ⟨δS, fun a => ?_⟩
  show (L (algebraMap A S a)).snd = _
  simp [L, h, Algebra.smul_def, -DualNumber.inr_eq_smul_eps]

theorem exists_der_fun {A S : Type} [CommRing A] [CommRing S] [Algebra A S] (M : Submonoid A) [IsLocalization M S]
    (δ : Derivation ℤ A A) : ∃ f : S →+ S, (∀ x y, f (x * y) = x * f y + y * f x) ∧
      ∀ a, f (algebraMap A S a) = algebraMap A S (δ a) := by
  obtain ⟨δS, hδS⟩ := exists_der_ext M δ (S := S)
  exact ⟨δS.toLinearMap.toAddMonoidHom, fun x y => by simp [Derivation.leibniz, smul_eq_mul], hδS⟩

theorem exists_der_frac (Ω : Type) [CommRing Ω] [IsDomain Ω] (δ : Derivation ℤ Ω Ω) :
    ∃ δS : Derivation ℤ (FractionRing Ω) (FractionRing Ω),
      ∀ ω, δS (algebraMap Ω (FractionRing Ω) ω) = algebraMap Ω (FractionRing Ω) (δ ω) := by
  obtain ⟨f, hf1, hf2⟩ := exists_der_fun (nonZeroDivisors Ω) δ (S := FractionRing Ω)
  have hf0 : f 1 = 0 := by
    have h11 := hf1 1 1
    rw [_root_.mul_one, _root_.one_mul] at h11
    linear_combination -h11
  have hfc : ∀ (c : ℤ) (y : FractionRing Ω), f ((c : FractionRing Ω) * y) = (c : FractionRing Ω) * f y := by
    intro c y
    have h2 : f (c : FractionRing Ω) = 0 := by
      rw [← zsmul_one, map_zsmul, hf0]
      simp
    rw [hf1, h2]
    simp
  refine ⟨{ toFun := f
            map_add' := f.map_add
            map_smul' := (fun c y => ?_)
            map_one_eq_zero' := hf0
            leibniz' := (fun x y => ?_) }, hf2⟩
  · simp only [RingHom.id_apply]
    rw [Algebra.smul_def, eq_intCast, zsmul_eq_mul]
    exact hfc c y
  · exact hf1 x y

theorem isKS_of_heat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D), IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) (fun a => spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) ≫ (tv (v' a)).left) (fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r))) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.mapMatrix h.Θ) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam hmon htt hab Y n vH dd hdd v' hv' D h hB hDef
  letI := H.starRing
  have hsm : Smooth Y.H.hom := GlobalTheory.RayTan.smooth_H R _ _ _ Y
  have hint : IsIntegral Y.H.left := GlobalTheory.T.isIntegral_raynaudExtension_noetherian_local R _ _ _ Y
  obtain ⟨i0, hi0⟩ : ∃ i0, ⊤ ≤ (η[Y.H]).left ⁻¹ᵁ h.W i0 := by
    have hm : (η[Y.H]).left (IsLocalRing.closedPoint R) ∈ ⨆ i, h.W i := by rw [h.cover]; trivial
    obtain ⟨i0, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
    exact ⟨i0, (ReciprocityTheory.ChartRestriction.G.DVR.eq_top_of_closedPoint_mem ((η[Y.H]).left ⁻¹ᵁ h.W i0) hi).ge⟩
  obtain ⟨Ω, _, _, _, φ, x, δ, dΩ, hΩc, hx, hxW, hdΩ, hδφ, hδ, hd, hinj⟩ :=
    GlobalTheory.T.exists_formalPoint_origin_smoothCommGroupScheme R Y.H hsm hint n vH dd hdd ⇑D (h.W i0) (h.d i0) (h.lift i0) hi0
  set e := Scheme.ΓSpecIso (CommRingCat.of R) with he
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    have h1 : valR x ⊤ (Y.H.hom.appTop.hom (e.inv.hom r)) = φ r := by
      refine (GlobalTheory.ZH.EvCrd.valR_comp x Y.H.hom ⊤ (by simp) _).trans ?_
      rw [hx]
      exact GlobalTheory.ZH.EvCrd.valR_fn φ r
    have h2 := GlobalTheory.PrimScale.valR_const (η[Y.H]).left Y.H.hom (Over.w η[Y.H]) r
    have h3 := hinj ⊤ _ (by simp) (h1.trans hr)
    rw [h3] at h2
    rw [← h2]
    simp [valR]

  obtain ⟨x', hx', dd', hdd', hδ', hinj', hpt⟩ :=
    GlobalTheory.T.exists_uniformisedGroup_point_sameDerivations E H R t P m tt gam hmon htt hab Y n vH dd hdd v' hv' Ω φ x δ hΩc hφ hx hδφ hδ
  obtain ⟨g, hg⟩ := ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_local (V := Ω) t.PP.L t.PP.isLB (K := PUnit)
    (fun _ => x' ≫ 𝟙 t.G.left) (fun _ => 1)
  have hex : ∀ a, ∃ δS : Derivation ℤ (FractionRing Ω) (FractionRing Ω),
      ∀ ω, δS (algebraMap Ω (FractionRing Ω) ω) = algebraMap Ω (FractionRing Ω) (δ a ω) :=
    fun a => exists_der_frac Ω (δ a)
  choose δL hδL using hex
  obtain ⟨dt, u', p, p', hdt, hact⟩ := GlobalTheory.T.commuting_heatOperators_act_on_values E H R t P m tt gam hmon htt hab Y n vH dd hdd v' hv' D h hB hDef
    i0 Ω φ x x' δ hΩc hx hx' hδφ hδ hpt dΩ hxW hd g hg δL hδL
  obtain ⟨b, rfl⟩ := GlobalTheory.T.tangentBasis_uniformisedGroup_of_raynaudExtension E H R t P Y n vH v' hv'
  let D₀ : Derivation ℤ Γ(Sp R, ⊤) Γ(Sp R, ⊤) := Derivation.mk'
    ((e.inv.hom.toAddMonoidHom.comp ((D : R →ₗ[ℤ] R).toAddMonoidHom.comp e.hom.hom.toAddMonoidHom)).toIntLinearMap)
    (fun a a' => by
      simp [Derivation.leibniz, smul_eq_mul])
  haveI := (isAffineOpen_top (Sp R)).isLocalization_basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))
  obtain ⟨DV, hDV⟩ := exists_der_ext (Submonoid.powers ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) D₀ (S := Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))))
  have hDV' : ∀ r, DV (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom (e.inv.hom r)) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom (e.inv.hom (D r)) := fun r => by
    show DV (algebraMap _ _ (e.inv.hom r)) = algebraMap _ _ (e.inv.hom (D r))
    rw [hDV]
    congr 1
    simp [D₀]

  obtain ⟨Θ₁, hsym, hKS⟩ := GlobalTheory.T.exists_symmetric_kodairaSpencer_abelianLocus E H R t P m tt gam hmon htt hab n b DV
  obtain ⟨iota, dt₂, u₂, p₂, p₂', hiota, hdt₂, hact₂⟩ := GlobalTheory.T.heatOperators_kodairaSpencer_formal_point_values E H R t P m tt gam hmon htt hab n b D Ω φ x' δ dd'
    hΩc hx' hdd' hδφ hδ' hinj' g hg δL hδL Θ₁ DV hDV' hKS
  have heq := GlobalTheory.T.heatOperator_symbol_unique_principalPolarisation E H R t P m tt gam hmon htt hab n b D Ω φ x' δ dd' hΩc hx' hdd' hδφ hδ' hinj' g hg δL hδL
    (((algebraMap Ω (FractionRing Ω)).comp φ).mapMatrix h.Θ) (iota.mapMatrix Θ₁) dt dt₂ u' u₂ p p' p₂ p₂'
    (by rw [RingHom.mapMatrix_apply, ← Matrix.transpose_map, h.symm])
    (by rw [RingHom.mapMatrix_apply, ← Matrix.transpose_map, hsym])
    (fun r => (hdt r).trans (hdt₂ r).symm) hact hact₂
  have hi : Function.Injective iota := by
    have key : ∀ y : Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))), iota y = 0 → y = 0 := by
      intro y hy
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (S := Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))) (Submonoid.powers ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) y
      dsimp only at hy ⊢
      have h1 : iota (algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) a) = 0 := by
        rw [← IsLocalization.mk'_spec (S := Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))) a s]
        erw [map_mul, hy, zero_mul]
      have h2 : (algebraMap Γ(Sp R, ⊤) _ a : Γ(Sp R, (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))) = ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom (e.inv.hom (e.hom.hom a)) := by
        rw [Iso.hom_inv_id_apply]
        rfl
      rw [h2, hiota] at h1
      have h3 : φ (e.hom.hom a) = 0 := IsFractionRing.injective Ω (FractionRing Ω) (by rw [h1, map_zero])
      have h4 : e.hom.hom a = 0 := hφ (by rw [h3, map_zero])
      have h5 : a = 0 := by simpa using congrArg e.inv.hom h4
      rw [h5, IsLocalization.mk'_zero]
    exact (injective_iff_map_eq_zero iota).2 key
  have hΘ : Θ₁ = (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp e.inv.hom).mapMatrix h.Θ := by
    ext a a'
    apply hi
    have := congrFun (congrFun heq a) a'
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.comp_apply] at this ⊢
    rw [← this, hiota]
  rw [hΘ] at hKS
  exact GlobalTheory.T.isKodairaSpencer_affineChart_of_basicOpen E H R t m tt n ⇑b D DV h.Θ hDV' hKS

end GlobalTheory.KBracket
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencer_of_commuting_heat_operators_raynaud : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D), IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens) (fun a => spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) ≫ (tv (v' a)).left) (fun r => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r))) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.mapMatrix h.Θ) := by
  atlas_forward_decl GlobalTheory.KBracket.isKS_of_heat
end
