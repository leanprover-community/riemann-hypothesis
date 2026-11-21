import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.QuadraticFormShiftExpand
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.QuaternaryFormUnitScaling

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

variable {F : Type} [Field F] [NumberField F]

private theorem quadraticForm_neg (δ : F) (y : V4 F) : q4 δ (-y) = q4 δ y := by
  simp only [q4, Pi.neg_apply]
  ring

private theorem quaternaryForm_neg_right (δ : F) (y v : V4 F) : B4 δ (-y) (-v) = B4 δ y v := by
  simp only [B4, Pi.neg_apply]
  ring

theorem UpperTheory.ConvolutionTheory.R2.C.gaussOp :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F), δ ≠ 0 → ∀ (b : (A F)ˣ) (c : ℂ), IsIdx δ (b : A F) c → ∀ (φ : S4 F) (v : V4 F),
    Pc δ (b : A F) φ.1 v = c * ft4 δ (fun y => ψ (-(((b⁻¹ : (A F)ˣ) : A F) * q4 δ y)) * ft4 δ φ.1 y) v := by
  intro F _ _ δ hδ b c hc φ v
  have hmem := (pcMem F δ).2 hδ b φ.1 φ.2
  have h2 := (ftBasic F δ hδ _ hmem).2.1 (-v)
  rw [neg_neg] at h2
  rw [← h2]
  have e1 : ∀ y, ft4 δ (Pc δ (b : A F) φ.1) y * ψ (B4 δ y (-v)) =
      c * ψ (-(((b⁻¹ : (A F)ˣ) : A F) * q4 δ y)) * ft4 δ φ.1 (-y) * ψ (B4 δ y (-v)) := fun y => by
    rw [idxFt F δ b c hc φ y]
  conv_lhs => rw [ft4]
  simp only [e1]
  rw [← integral_neg_eq_self _ (adeleMeasurePi F)]
  simp only [neg_neg, quadraticForm_neg, quaternaryForm_neg_right]
  rw [ft4, ← integral_const_mul]
  congr 1
  funext y
  ring
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.opsGauss :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (η : (A F)ˣ →* ℂˣ) (O : Ops δ η), δ ≠ 0 → (∀ a, η a ^ 2 = 1) →
    (∀ b : (A F)ˣ, IsIdx δ (b : A F) (((η b : ℂˣ) : ℂ) * (((ab b)⁻¹ ^ 2 : ℝ) : ℂ))) → Gauss O.N O.M O.W := by
  intro F _ _ δ η O hδ hη hidx t
  obtain ⟨b, hb⟩ : ∃ b : (A F)ˣ, b = -t⁻¹ := ⟨_, rfl⟩
  have hbc : -((t⁻¹ : (A F)ˣ) : A F) = (b : A F) := by simp [hb]
  have htb : -(((b⁻¹ : (A F)ˣ) : A F)) = (t : A F) := by simp [hb]
  rw [hbc, ← hb]
  refine LinearMap.ext fun φ => Subtype.ext (funext fun v => ?_)
  simp only [Module.End.mul_apply]
  have hL : (O.W (O.N (t : A F) (O.W φ))).1 v =
      ft4 δ (fun y => ψ ((t : A F) * q4 δ y) * ft4 δ φ.1 y) v := by
    rw [O.W_apply]
    congr 1
    funext y
    rw [O.N_apply, O.W_apply]
  have hR : (O.N (b : A F) (O.M b (O.W (O.N (b : A F) φ)))).1 v =
      ((η b : ℂˣ) : ℂ) * ((ab b ^ 2 : ℝ) : ℂ) * Pc δ (b : A F) φ.1 v := by
    rw [O.N_apply, O.M_apply, O.W_apply, (pcMem F δ).1]
    have : (fun y => (O.N (b : A F) φ).1 y) = fun x => ψ ((b : A F) * q4 δ x) * φ.1 x :=
      funext fun y => O.N_apply _ _ _
    have h2 : (O.N (b : A F) φ).1 = fun x => ψ ((b : A F) * q4 δ x) * φ.1 x := this
    rw [h2]
    ring
  have hG := gaussOp F δ hδ b _ (hidx b) φ v
  have hη2 : ((η b : ℂˣ) : ℂ) ^ 2 = 1 := by
    have := congrArg (fun u : ℂˣ => (u : ℂ)) (hη b)
    simpa using this
  have hab : ab b ≠ 0 := by
    have : 0 < ab b := (IdeleGroup.ideleModule F b).2
    exact this.ne'
  have habc : ((ab b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hab
  have hfn : (fun y => ψ (-(((b⁻¹ : (A F)ˣ) : A F) * q4 δ y)) * ft4 δ φ.1 y) =
      fun y => ψ ((t : A F) * q4 δ y) * ft4 δ φ.1 y := by
    funext y
    rw [← htb, neg_mul]
  rw [hfn] at hG
  rw [hL, hR, hG]
  push_cast
  field_simp
  rw [hη2]
  ring
end
