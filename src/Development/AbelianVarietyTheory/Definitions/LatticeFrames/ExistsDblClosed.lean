import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmHostImaginaryGeneratorNeZero

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocMod.PinModel

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


theorem exists_dbl (p : Place D k) {σ : ℕ} (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (n₀ n₁ n₂ : Type)
    [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] {s : k} (hs : s ≠ 0)
    (F₀ : GlobalTheory.LocMod.Frame k B.A.rank n₀) (F₁ : GlobalTheory.LocMod.Frame k J.W₀.rank n₁) (F₂ : GlobalTheory.LocMod.Frame k B'.A.rank n₂) :
    ∃ F : Dbl p B J B' n₀ n₁ n₂ (2 * σ), F.s = s ∧ F.F₀ = F₀ ∧ F.F₁ = F₁ ∧ F.F₂ = F₂ := by
  obtain ⟨G₀, h₀⟩ := Witness.exists_bes p B hs F₀
  obtain ⟨G₁, h₁⟩ := Witness.exists_jac p J hs (Witness.hz_ne p B) F₁
  obtain ⟨G₂, h₂⟩ := Witness.exists_bes p B' (mul_ne_zero hs (Witness.xi_ne p)) F₂
  exact ⟨⟨s, hs, F₀, F₁, F₂, G₀, G₁, G₂, h₀, h₁, h₂⟩, rfl, rfl, rfl, rfl⟩



variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem exists_isOne : ∃ Φ : SB (Matrix Y Y' k), IsOne Φ ∧ Φ.1 0 = 1 := by
  refine ⟨⟨Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1, mem_SB_of_periodic (fun x hx => ?_) fun x y hy => ?_⟩, rfl, ?_⟩
  · exact (Set.mem_of_indicator_ne_zero hx)
  · have : (∀ r q, (x + y) r q ∈ 𝒪[k]) ↔ ∀ r q, x r q ∈ 𝒪[k] :=
      ⟨fun h r q => by simpa using sub_mem (h r q) (hy.intM r q), fun h r q => add_mem (h r q) (hy.intM r q)⟩
    by_cases hx : ∀ r q, x r q ∈ 𝒪[k]
    · rw [Set.indicator_of_mem (by exact this.2 hx), Set.indicator_of_mem (by exact hx)]
    · rw [Set.indicator_of_notMem (by exact fun h => hx (this.1 h)), Set.indicator_of_notMem (by exact hx)]
  · simp

theorem isCombAt_one (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (FS : GlobalTheory.LocMod.Frame k S.rank Y')
    (FT : GlobalTheory.LocMod.Frame k T.rank Y) :
    p.IsCombAt ψ FS FT (Finsupp.single 0 1) (Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} fun _ => 1) := by
  refine ⟨fun u hu => ?_, fun Tm _ Φ₀ Φ h₀ h => ?_⟩
  · rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hu
    subst hu; intro i j; simp
  · obtain rfl : Φ = Φ₀ := Subtype.ext (h.trans h₀.symm)
    funext w
    simp [comb, Finsupp.support_single_ne_zero, heisO, symplOH, symplO, hO]

theorem toEAf_surj (D : D7) : Function.Surjective (toEAf D) := by
  refine (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).surjective.comp ?_
  exact Algebra.TensorProduct.map_surjective _ _ (fun α => ⟨pairA _ 0 α, rfl⟩) Function.surjective_id

theorem pi_congr (p : Place D k) {a b : Formalism.L2.Theta.AE D} (h : toEAf D a = toEAf D b) : p.π a = p.π b := by
  have h1 : finPart D a = finPart D b := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective h
  have h2 : p.e * a = p.e * b := GlobalTheory.SplitScalar.adele_ext (by rw [map_mul, map_mul, GlobalTheory.SplitScalar.infPart_splitIdem p.split, zero_mul, zero_mul])
    (by rw [map_mul, map_mul, h1])
  rw [← p.π_ι (p.π a), p.ι_π, h2, ← p.ι_π, p.π_ι]

theorem exists_movedTo (p : Place D k) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) {M M' : Matrix (Fin V.rank) (Fin V.rank) k}
    (hM : M * M' = 1) : ∃ g, SuppAt p.e V g ∧ MovedTo p V g β M := by
  choose f hf using toEAf_surj D
  have key : ∀ b : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D), b.map (toEAf D) = β.val →
      ((β⁻¹).val.map f).map p.π * b.map p.π = 1 := fun b hb => by
    have e : ((β⁻¹).val.map f * b).map (toEAf D) = (1 : Matrix _ _ (Formalism.L2.Theta.AE D)).map (toEAf D) := by
      rw [Matrix.map_mul, hb, show ((β⁻¹).val.map f).map (toEAf D) = (β⁻¹).val from by ext i j; exact hf _, Units.inv_mul,
        Matrix.map_one _ (map_zero _) (map_one _)]
    rw [← Matrix.map_mul, ← Matrix.map_one p.π (map_zero _) (map_one _)]
    ext i j
    exact pi_congr p (congrFun (congrFun e i) j)
  have k0 := key (β.val.map f) (by ext i j; exact hf _)
  have h1 : M * ((β⁻¹).val.map f).map p.π * ((β.val.map f).map p.π * M') = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ _ M', k0, Matrix.one_mul, hM]
  obtain ⟨g, hg, hg'⟩ := Witness.exists_isLoc p (S := V) (Frame.ofGL 1) ⟨_, _, h1, mul_eq_one_comm.1 h1⟩
  refine ⟨g, hg, fun b hb => ?_⟩
  rw [Matrix.map_mul, hg']
  simp only [Frame.ofGL, Units.val_one, inv_one, Matrix.one_mul, Matrix.mul_one]
  rw [Matrix.mul_assoc, key b hb, Matrix.mul_one]


theorem exists_ord (κ l τ j N : ℕ) (h : Fintype.card (Ix (Fin κ ⊕ Fin l) (Fin τ) j) = N) :
    ∃ e : Ix (Fin κ ⊕ Fin l) (Fin τ) j ≃ Fin N, GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e := by
  have h' : κ + l + j * τ = N := by simpa using h
  refine ⟨((finSumFinEquiv.sumCongr finProdFinEquiv).trans finSumFinEquiv).trans (finCongr h'), ?_⟩
  rintro ((i | i) | ⟨a, b⟩) <;> simp [GlobalTheory.SymBridge.zPos]
  ring

variable {u : D.what₂.Word}


end GlobalTheory.LocMod.PinModel
end
