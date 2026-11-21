import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
import GroundTheory.GlobalFields.TateThesis.TateThetaDecay

section
noncomputable section

open NumberField
open scoped SchwartzMap ContDiff

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

def curryE : (Fin 2 → UpperTheory.V.TR.Rinf F) ≃ₗ[ℝ] (Fin 2 × InfinitePlace F → ℝ) where
  toFun y p := y p.1 p.2
  invFun z i v := z (i, v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def euclE : (Fin 2 → UpperTheory.V.TR.Rinf F) ≃L[ℝ] EuclideanSpace ℝ (Fin 2 × InfinitePlace F) :=
  (curryE F).toContinuousLinearEquiv.trans (EuclideanSpace.equiv (Fin 2 × InfinitePlace F) ℝ).symm

omit [IsTotallyReal F] in
theorem norm_euclE_sq (y : Fin 2 → UpperTheory.V.TR.Rinf F) :
    ‖euclE F y‖ ^ 2 = ∑ v, ((y 0 v) ^ 2 + (y 1 v) ^ 2) := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, Fin.sum_univ_two,
    ← Finset.sum_add_distrib]
  rfl

def gaussV : 𝓢(Fin 2 → UpperTheory.V.TR.Rinf F, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclE F) (GroundTheory.Global.gaussianSchwartz _)

theorem gaussV_apply (y : Fin 2 → UpperTheory.V.TR.Rinf F) :
    gaussV F y = Complex.exp (-(Real.pi : ℂ) * ∑ v, (((y 0 v : ℝ) : ℂ) ^ 2 + ((y 1 v : ℝ) : ℂ) ^ 2)) := by
  simp only [gaussV, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    GroundTheory.Global.gaussianSchwartz_apply, norm_euclE_sq]
  push_cast
  rfl

def coordV (i : Fin 2) (v : InfinitePlace F) : (Fin 2 → UpperTheory.V.TR.Rinf F) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : InfinitePlace F => ℝ) v).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => UpperTheory.V.TR.Rinf F) i)

def linV (v : InfinitePlace F) : (Fin 2 → UpperTheory.V.TR.Rinf F) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (coordV F 0 v) + Complex.I • Complex.ofRealCLM.comp (coordV F 1 v)

theorem linV_apply (v : InfinitePlace F) (y : Fin 2 → UpperTheory.V.TR.Rinf F) :
    linV F v y = ((y 0 v : ℝ) : ℂ) + Complex.I * ((y 1 v : ℝ) : ℂ) := by
  simp [linV, coordV]

def polyV (y : Fin 2 → UpperTheory.V.TR.Rinf F) : ℂ := ∏ v, linV F v y

theorem polyV_hasTemperateGrowth : (polyV F).HasTemperateGrowth := by
  classical
  have h : ∀ s : Finset (InfinitePlace F),
      (fun y : Fin 2 → UpperTheory.V.TR.Rinf F => ∏ v ∈ s, linV F v y).HasTemperateGrowth := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp only [Finset.prod_empty]; exact Function.HasTemperateGrowth.const (E := Fin 2 → UpperTheory.V.TR.Rinf F) (1 : ℂ)
    | insert a s ha ih =>
      have e : (fun y : Fin 2 → UpperTheory.V.TR.Rinf F => ∏ v ∈ insert a s, linV F v y) =
          (fun y => linV F a y) * (fun y => ∏ v ∈ s, linV F v y) := by
        funext y
        rw [Finset.prod_insert ha]
        rfl
      rw [e]
      exact (linV F a).hasTemperateGrowth.mul ih
  exact h Finset.univ

def archS : 𝓢(Fin 2 → UpperTheory.V.TR.Rinf F, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (polyV F) (gaussV F)

theorem archS_apply (y : Fin 2 → UpperTheory.V.TR.Rinf F) : archS F y = arch (y 0) (y 1) := by
  rw [archS, SchwartzMap.smulLeftCLM_apply_apply (polyV_hasTemperateGrowth F), gaussV_apply,
    smul_eq_mul, polyV, arch, Finset.prod_mul_distrib, Finset.mul_sum, Complex.exp_sum]
  simp only [linV_apply]

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
end
end

section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap ContDiff
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

abbrev Vr (F : Type) [Field F] [NumberField F] : Type := Fin 2 → UpperTheory.V.TR.Rinf F

def Xi (F : Type) [Field F] : Type := {ξ : Fin 2 → F // ξ ≠ 0}

instance : MeasurableSpace (Xi F) := ⊤

instance : MeasurableSingletonClass (Xi F) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

instance : Countable F := (Module.finBasis ℚ F).equivFun.toEquiv.injective.countable

instance : Countable (Xi F) := inferInstanceAs (Countable {ξ : Fin 2 → F // ξ ≠ 0})

abbrev Pp (F : Type) [Field F] [NumberField F] : Type := {r : ℝ // 0 < r} × normOneSubgroup F

def av (p : Pp F) : Ideles F := moduleSection (w0 F) p.1 * (p.2 : Ideles F)

def μS (F : Type) [Field F] [NumberField F] (S : Set {r : ℝ // 0 < r}) : Measure (Pp F × Xi F) :=
  ((posRealMeasure.restrict S).prod ((normOneMeasure F).restrict (normOneFundamentalDomain F))).prod
    Measure.count

def Mrow (g : GA F 2) (a : Ideles F) : GA F 2 := Matrix.GeneralLinearGroup.scalar (Fin 2) a * g

def Mcol (g : GA F 2) (a : Ideles F) : GA F 2 := g⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹

def rowv (g : GA F 2) (a : Ideles F) (ξ : Fin 2 → F) : Fin 2 → Ad F :=
  rowA ξ ᵥ* ((Mrow g a : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))

def colv (g : GA F 2) (a : Ideles F) (ξ : Fin 2 → F) : Fin 2 → Ad F :=
  ((Mcol g a : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ

open Classical in

def finRow (c : HeightOneSpectrum (𝓞 F) → ℕ) (y : Fin 2 → Ad F) : ℂ :=
  if ∀ w, Valued.v (pLoc F w (pFin F (y 0))) ≤ WithZero.exp (-(c w : ℤ)) ∧
      Valued.v (pLoc F w (pFin F (y 1)) - 1) ≤ WithZero.exp (-(c w : ℤ)) then 1 else 0

open Classical in

def finCol (c : HeightOneSpectrum (𝓞 F) → ℕ) (y : Fin 2 → Ad F) : ℂ :=
  if ∀ w, Valued.v (pLoc F w (pFin F (y 0))) ≤ WithZero.exp ((c w : ℤ) + dd w) ∧
      Valued.v (pLoc F w (pFin F (y 1))) ≤ WithZero.exp ((c w : ℤ) + dd w)
  then ((finiteAdelicChar F (pFin F (y 1)) : Circle) : ℂ) else 0

def vInf (y : Fin 2 → Ad F) : Vr F := fun i => UpperTheory.V.TR.pInf F (y i)

def kap1 (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (q : Pp F × Xi F) : ℂ :=
  finRow c (rowv g (av q.1) q.2.1) * ((χ.1 (av q.1) : ℂˣ) : ℂ)⁻¹ * ((q.1.1 : ℝ) : ℂ)

def w1 (g : GA F 2) (q : Pp F × Xi F) : Vr F := vInf (rowv g (av q.1) q.2.1)

def kap2 (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (q : Pp F × Xi F) : ℂ :=
  finCol c (colv g (av q.1) q.2.1) * ((χ.1 (av q.1) : ℂˣ) : ℂ)⁻¹ * ((q.1.1 : ℝ) : ℂ)⁻¹

def w2 (g : GA F 2) (q : Pp F × Xi F) : Vr F := vInf (colv g (av q.1) q.2.1)

def B1lin : Vr F →ₗ[ℝ] UpperTheory.V.TR.Lie F 2 →ₗ[ℝ] Vr F :=
  LinearMap.mk₂ ℝ (fun w x => w ᵥ* Matrix.of x)
    (fun w w' x => Matrix.add_vecMul _ _ _) (fun r w x => Matrix.smul_vecMul _ _ _)
    (fun w x x' => by exact Matrix.vecMul_add _ _ _)
    (fun r w x => by exact Matrix.vecMul_smul (R := ℝ) _ _ _)

def B2lin : Vr F →ₗ[ℝ] UpperTheory.V.TR.Lie F 2 →ₗ[ℝ] Vr F :=
  LinearMap.mk₂ ℝ (fun w z => Matrix.of z *ᵥ w)
    (fun w w' z => Matrix.mulVec_add _ _ _) (fun r w z => Matrix.mulVec_smul _ _ _)
    (fun w z z' => by exact Matrix.add_mulVec _ _ _)
    (fun r w z => by exact Matrix.smul_mulVec (R := ℝ) _ _ _)

def B1 : Vr F →L[ℝ] UpperTheory.V.TR.Lie F 2 →L[ℝ] Vr F :=
  LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ B1lin)

def B2 : Vr F →L[ℝ] UpperTheory.V.TR.Lie F 2 →L[ℝ] Vr F :=
  LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ B2lin)

@[simp] theorem left_bilinear_apply (w : Vr F) (x : UpperTheory.V.TR.Lie F 2) : B1 w x = w ᵥ* Matrix.of x := rfl

@[simp] theorem right_bilinear_apply (w : Vr F) (z : UpperTheory.V.TR.Lie F 2) : B2 w z = Matrix.of z *ᵥ w := rfl

def invL (x : UpperTheory.V.TR.Lie F 2) : UpperTheory.V.TR.Lie F 2 := UpperTheory.V.TR.toL (Matrix.of x)⁻¹

def dl (g : GA F 2) (x : UpperTheory.V.TR.Lie F 2) : ℝ := absD g * ∏ v, (Matrix.det (Matrix.of x)) v

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
end
end
