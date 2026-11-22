module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolActs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDualPairSwapSymmetry
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFinitePiTensorSumOfFactorOperators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchrodingerMapExistsOfArchHeisenbergDerivaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivatiStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLawsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupGeneratorsExistStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieScalar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExistsStatement

@[expose] public section

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PolActsPf

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.RealActs

section Swap

variable {P Q R S : ℕ}

def flipE (P Q R S : ℕ) : Formalism.BasicNotions.TH.Pol R S P Q ≃ₗ[ℂ] Formalism.BasicNotions.TH.Pol P Q R S :=
  (MvPolynomial.renameEquiv ℂ (Equiv.prodComm (Ix R S) (Ix P Q))).toLinearEquiv

theorem lineSign_flip (a : Ix P Q) (b : Ix R S) :
    lineSign (p := R) (q := S) (r := P) (s := Q) b a = lineSign (p := P) (q := Q) (r := R) (s := S) a b := by
  rcases a with a | a <;> rcases b with b | b <;> rfl

theorem flipE_heisOp (c : Matrix (Ix R S) (Ix P Q) ℂ) (f : Formalism.BasicNotions.TH.Pol R S P Q) :
    flipE P Q R S (heisOp c f) = heisOp cᵀ (flipE P Q R S f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [heisOp, flipE_apply, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sub_apply,
    map_smul, map_sum, map_sub, GlobalTheory.FockSwap.rename_raiB, GlobalTheory.FockSwap.rename_lowB]
  congr 1
  refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun l => ?_
  simp [lineSign_flip]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def flipT (ι : Type) (P Q R S : ℕ) :
    (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol R S P Q) ≃ₗ[ℂ] ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S :=
  PiTensorProduct.congr fun _ => flipE P Q R S

theorem flipT_atPl (w : ι) (L' : Module.End ℂ (Formalism.BasicNotions.TH.Pol R S P Q)) (L : Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))
    (h : ∀ f, flipE P Q R S (L' f) = L (flipE P Q R S f)) (T : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol R S P Q) :
    flipT ι P Q R S (atPl w L' T) = atPl w L (flipT ι P Q R S T) := by
  have e : (flipT ι P Q R S).toLinearMap ∘ₗ atPl w L' = atPl w L ∘ₗ (flipT ι P Q R S).toLinearMap := by
    refine PiTensorProduct.ext (MultilinearMap.ext fun x => ?_)
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, atPl, flipT,
      PiTensorProduct.map_tprod, PiTensorProduct.congr_tprod]
    congr 1
    funext i
    by_cases hi : i = w
    · subst hi; simp [h]
    · simp [Function.update_of_ne hi]
  exact LinearMap.congr_fun e T

theorem flipT_sumPl (L' : ι → Module.End ℂ (Formalism.BasicNotions.TH.Pol R S P Q)) (L : ι → Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))
    (h : ∀ w f, flipE P Q R S (L' w f) = L w (flipE P Q R S f)) (T : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol R S P Q) :
    flipT ι P Q R S (sumPl L' T) = sumPl L (flipT ι P Q R S T) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [sumPl, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun w _ => flipT_atPl w (L' w) (L w) (h w) T

end Swap

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isFockMap_flip {σ : E →ₐ[F] E} {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
    {P Q R S : ℕ} {ψ : AddChar (AF F) ℂ} {τ : ∀ w : InfinitePlace F, EmbOver E w} {JA : Matrix α α (AE F E)}
    {JB : Matrix β β (AE F E)} {d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ}
    {d' : Darboux (symp (R := AF F) (cA σ) (-1) JB JA) κ} {A : InfinitePlace F → Matrix α (Ix P Q) ℂ}
    {C : InfinitePlace F → Matrix β (Ix R S) ℂ} {Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ} (hΦ : IsFockMap ψ τ d A C Φ)
    (hdd : ∀ x : Matrix α β (AE F E), d'.e xᵀ = d.e x) :
    IsFockMap ψ τ d' C A (Φ ∘ₗ (flipT (InfinitePlace F) P Q R S).toLinearMap) := by
  refine ⟨hΦ.1.comp (flipT (InfinitePlace F) P Q R S).injective, fun u hu c hc T => ?_⟩
  have hu' : At (evI F) uᵀ := fun x hx => by rw [← Matrix.transpose_smul, hu x hx, Matrix.transpose_zero]
  have hc' : ∀ w, uᵀ.map (piInf (τ w)) = A w * (c w)ᵀ * (C w)ᵀ := fun w => by
    rw [Matrix.transpose_map, hc w]; simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have key := hΦ.2 uᵀ hu' (fun w => (c w)ᵀ) hc' (flipT (InfinitePlace F) P Q R S T)
  have hr : ∀ t : ℝ, d'.rho ψ (realAd F t • u) = d.rho ψ (realAd F t • uᵀ) := fun t => by
    show schr ψ (d'.e _) = schr ψ (d.e _)
    rw [← hdd, Matrix.transpose_smul, Matrix.transpose_transpose]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [flipT_sumPl (fun w => heisOp (c w)) (fun w => heisOp (c w)ᵀ) (fun w f => flipE_heisOp (c w) f)]
  set_option backward.isDefEq.respectTransparency false in
   rw [show (fun t : ℝ => d'.rho ψ (realAd F t • u)) =
    (fun t : ℝ => d.rho ψ (realAd F t • uᵀ)) from funext hr]
  exact key

theorem incM_map_real {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem locFin_compact (P Q R S : ℕ) (Y : Mat R S) (hY : IsKC Y) (c : ℂ) :
    LocFin (fockAct2 P Q R S Y + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs Y hY y hy) (W.smul_mem c hy)⟩

section Graph

variable {κ V : Type} [Fintype κ] [AddCommGroup V] [Module ℂ V] {Φ : V →ₗ[ℂ] SInf F κ}

theorem graph_of_inj (hΦ : Function.Injective Φ) (L : Module.End ℂ V) (Rel : SInf F κ → SInf F κ → Prop)
    (huniq : ∀ f f₁ f₂, Rel f f₁ → Rel f f₂ → f₁ = f₂) (h : ∀ v, Rel (Φ v) (Φ (L v))) :
    ∃ D : SInf F κ →ₗ[ℂ] SInf F κ, (∀ f ∈ LinearMap.range Φ, D f ∈ LinearMap.range Φ) ∧
      ∀ f ∈ LinearMap.range Φ, ∀ f₁ : SInf F κ, Rel f f₁ ↔ f₁ = D f := by
  obtain ⟨Ψ, hΨ⟩ := LinearMap.exists_leftInverse_of_injective Φ (LinearMap.ker_eq_bot.2 hΦ)
  refine ⟨Φ ∘ₗ L ∘ₗ Ψ, fun f _ => LinearMap.mem_range_self Φ _, ?_⟩
  rintro _ ⟨v, rfl⟩ f₁
  have e : (Φ ∘ₗ L ∘ₗ Ψ) (Φ v) = Φ (L v) := by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← LinearMap.comp_apply Ψ Φ, hΨ, LinearMap.id_apply]
  rw [e]
  exact ⟨fun h1 => huniq _ _ _ h1 (h v), fun h1 => h1 ▸ h v⟩

theorem derOn_of_sd (hΦ : Function.Injective Φ) (L : Module.End ℂ V) (T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ)
    (h0 : ∀ t, T t 0 = 0) (h : ∀ v, SD T (Φ v) (Φ (L v))) : DerOn (LinearMap.range Φ) T :=
  graph_of_inj hΦ L (fun f f₁ => ActsD (evI F) T f f₁) (fun f f₁ f₂ => (actsLaws F κ f f₁ f₂).2.2.1 T)
    fun v => (actsLaws F κ _ _ (Φ v)).1 T h0 (h v)

theorem opOn_of_sa (hΦ : Function.Injective Φ) (L : Module.End ℂ V) (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ)
    (h0 : T 0 = 0) (h : ∀ v, SA T (Φ v) (Φ (L v))) : OpOn (LinearMap.range Φ) T :=
  graph_of_inj hΦ L (fun f f₁ => Acts (evI F) T f f₁) (fun f f₁ f₂ => (actsLaws F κ f f₁ f₂).2.2.2.1 T)
    fun v => (actsLaws F κ _ _ (Φ v)).2.1 T h0 (h v)

end Graph

end GlobalTheory.PolActsPf

end
