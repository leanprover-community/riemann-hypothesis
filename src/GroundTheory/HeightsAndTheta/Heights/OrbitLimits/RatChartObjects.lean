import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StokesObjects
import GroundTheory.HeightsAndTheta.Heights.Intersections.StPtsAbsIntegrable

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

namespace PtsSegreChart

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def coordEquiv : (Σ k, ι k) ≃ Fin (Fintype.card (Σ k, ι k)) :=
  Fintype.equivFin _

def pt (x : Fin (Fintype.card (Σ k, ι k)) → ℂ) : (Σ k, ι k) → ℂ :=
  fun p => x (coordEquiv p)

def ideal (P : Ideal (MRing ι)) (i : (k : K) → ι k) :
    Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) :=
  Ideal.map ((rename (coordEquiv (ι := ι))).toRingHom.comp (map (Int.castRingHom ℂ))) P ⊔
    Ideal.span (Set.range fun k => (X (coordEquiv ⟨k, i k⟩) - 1 : MvPolynomial _ ℂ))

def chartPot {e : ℕ} (L : Fin e → HermLine ι) : Fin e → (Fin (Fintype.card (Σ k, ι k)) → ℂ) → ℝ :=
  fun j x => Real.log ((L j).h (pt x))

def weight (u : ((Σ k, ι k) → ℂ) → ℝ) (A : HermLine ι) (s : MRing ι) :
    (Fin (Fintype.card (Σ k, ι k)) → ℂ) → ℝ :=
  {x | ∀ k, ∃ j, pt x ⟨k, j⟩ ≠ 0}.indicator fun x => u (pt x) * logNorm A s (pt x)

end PtsSegreChart

def PtsSegreChart.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι) (u : ((Σ k, ι k) → ℂ) → ℝ)
    (i : (k : K) → ι k) (δ : ℝ),
    IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSectionOn P A s →
    IsDegZeroSmooth u → 0 < δ → (∀ z, ‖segre z i‖ < δ * ‖segre z‖ → u z = 0) →
    ∀ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ →
      Integrable (fun y =>
        ∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ (pot L) (fun z => u z * logNorm A s z) y w) ∧
      ptsIntegralAt P Ψ (pot L) (fun z => u z * logNorm A s z) =
        ∑ᶠ J ∈ (PtsSegreChart.ideal P i).minimalPrimes,
          varInt J e (PtsSegreChart.weight u A s) (PtsSegreChart.chartPot L)

end GroundTheory.Heights₂.Heights
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

def PtsChartCompare.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (e : ℕ) (L : Fin e → HermLine ι) (g : ((Σ k, ι k) → ℂ) → ℝ) (i : (k : K) → ι k) (δ : ℝ),
    IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) →
    Measurable ({z : (Σ k, ι k) → ℂ | ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0}.indicator g) →
    (∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → g (fun p => c p.1 * z p) = g z) →
    0 < δ → (∀ z, ‖segre z i‖ < δ * ‖segre z‖ → g z = 0) →
    ∀ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ →
      Integrable (fun y => ∑ᶠ w ∈ fibre P Ψ y, |sheetDensity P Ψ (pot L) g y w|) →
      Integrable (fun y => ∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ (pot L) g y w) →
      ptsIntegralAt P Ψ (pot L) g =
        ∑ᶠ J ∈ (PtsSegreChart.ideal P i).minimalPrimes,
          varInt J e
            ({x | ∀ k, ∃ j, PtsSegreChart.pt x ⟨k, j⟩ ≠ 0}.indicator fun x => g (PtsSegreChart.pt x))
            (PtsSegreChart.chartPot L)

end GroundTheory.Heights₂.Heights
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ComplexSets

namespace RatChart

variable {n d : ℕ}

def ratMap (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) : Fin d → ℂ :=
  fun r => eval x (p r) / eval x q

def ratFibre (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ)
    (q : MvPolynomial (Fin n) ℂ) (y : Fin d → ℂ) : Set (Fin n → ℂ) :=
  {x | x ∈ zeroSet J ∧ eval x q ≠ 0 ∧ ratMap p q x = y}

def IsRatSheetAt (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ)
    (q : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) (s : (Fin d → ℂ) → Fin n → ℂ) : Prop :=
  ∃ U : Set (Fin d → ℂ), IsOpen U ∧ ratMap p q x ∈ U ∧ DifferentiableOn ℂ s U ∧ s (ratMap p q x) = x ∧
    (∀ y ∈ U, s y ∈ zeroSet J ∧ eval (s y) q ≠ 0 ∧ ratMap p q (s y) = y) ∧
    ∃ V ∈ 𝓝 x, ∀ x' ∈ zeroSet J ∩ V, eval x' q ≠ 0 → ratMap p q x' ∈ U → x' = s (ratMap p q x')

open Classical in

def ratSheetSum (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ)
    (q : MvPolynomial (Fin n) ℂ) (F : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ) (y : Fin d → ℂ) : ℝ :=
  ∑ᶠ (x : Fin n → ℂ) (_ : x ∈ ratFibre J p q y),
    if h : ∃ s, IsRatSheetAt J p q x s then F x h.choose else 0

def ratDens (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ)
    (q : MvPolynomial (Fin n) ℂ) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) : ℝ :=
  ratSheetSum J p q (fun x s => f x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y) y

def ratAbsDens (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ)
    (q : MvPolynomial (Fin n) ℂ) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) : ℝ :=
  ratSheetSum J p q (fun x s => |f x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) y|) y

end RatChart

namespace PtsSegreChart

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def segrePoly (a : (k : K) → ι k) : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ :=
  ∏ k, X (coordEquiv ⟨k, a k⟩)

open Classical in

def projPoly {e : ℕ} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (r : Fin (e + 1)) :
    MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ :=
  ∑ a, C (Ψ (fun b => if a = b then 1 else 0) r) * segrePoly a

def chartNum {e : ℕ} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    Fin e → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ :=
  fun r => projPoly Ψ r.succ

def chartDen {e : ℕ} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ :=
  projPoly Ψ 0

omit [DecidableEq K] in

def chartWeight (g : ((Σ k, ι k) → ℂ) → ℝ) : (Fin (Fintype.card (Σ k, ι k)) → ℂ) → ℝ :=
  {x | ∀ k, ∃ j, pt x ⟨k, j⟩ ≠ 0}.indicator fun x => g (pt x)

end PtsSegreChart

end GroundTheory.Heights₂.Heights
end
end
