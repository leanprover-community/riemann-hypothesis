module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot

@[expose] public section

noncomputable section

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.SmoothTranslate

theorem conj_mem_lieG {n : ℕ} {J g X : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit g) (hg : g ∈ Formalism.QuantumDeterminants.UH J)
    (hX : X ∈ lieG J) : g⁻¹ * X * g ∈ lieG J := by
  have hd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hu
  have hAB : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul _ hd
  have hBA : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have hBA' : (g⁻¹)ᴴ * gᴴ = 1 := by rw [← conjTranspose_mul, hBA, conjTranspose_one]
  have h : gᴴ * J * g = J := hg
  have hX' : Xᴴ * J + J * X = 0 := hX
  show (g⁻¹ * X * g)ᴴ * J + J * (g⁻¹ * X * g) = 0
  calc (g⁻¹ * X * g)ᴴ * J + J * (g⁻¹ * X * g)
      = (g⁻¹ * X * g)ᴴ * (gᴴ * J * g) + (gᴴ * J * g) * (g⁻¹ * X * g) := by rw [h]
    _ = gᴴ * (Xᴴ * ((g⁻¹)ᴴ * gᴴ) * J + J * (g * g⁻¹) * X) * g := by
        simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [hBA, hBA', Matrix.mul_one, Matrix.mul_one, hX', Matrix.mul_zero, Matrix.zero_mul]

theorem mul_prod_conj {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit g)
    (l : List (Matrix (Fin n) (Fin n) ℂ)) : g * (l.map fun x => g⁻¹ * x * g).prod = l.prod * g := by
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 hu
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, Matrix.mul_assoc x, ← ih]
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]

theorem smoothVec_translate : ∀ {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {J : Matrix (Fin n) (Fin n) ℂ} (hJ : IsUnit J) {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH J) σ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH J) {v : H}
    (hv : SmoothVec (lieG J) σ v), SmoothVec (lieG J) σ (σ g v) := by
  intro n H _ _ J hJ σ hσ g hg v hv k Xs hXs
  have hu : IsUnit g := isUnit_of_mem_UH hJ hg
  have hY : ∀ i, g⁻¹ * Xs i * g ∈ lieG J := fun i => conj_mem_lieG hu hg (hXs i)
  have hc : ∀ (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ),
      NormedSpace.exp (t • (g⁻¹ * X * g)) = g⁻¹ * NormedSpace.exp (t • X) * g := fun X t => by
    rw [← Matrix.exp_conj' _ _ hu, Matrix.mul_smul, Matrix.smul_mul]
  have h1 := ((σ g).restrictScalars ℝ).contDiff.comp (hv k _ hY)
  convert h1 using 2 with t
  show σ _ (σ g v) = σ g (σ _ v)
  have hP := expProd_mem_UH hJ hXs t
  have hQ := expProd_mem_UH hJ hY t
  have e1 := hσ.1.2 _ hP _ hg
  have e2 := hσ.1.2 _ hg _ hQ
  have e3 : g * (List.ofFn fun i => NormedSpace.exp (t i • (g⁻¹ * Xs i * g))).prod
      = (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * g := by
    rw [← mul_prod_conj hu, List.map_ofFn]
    simp only [hc, Function.comp_def]
  have e4 := e1.symm.trans ((congrArg σ e3).symm.trans e2)
  exact congrArg (fun T : H →L[ℂ] H => T v) e4

end UpperTheory.Lit.Bur.SmoothTranslate

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

theorem _root_.UpperTheory.Lit.Bur.smoothVec_stable_under_unitaryGroup : ∀ {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {J : Matrix (Fin n) (Fin n) ℂ} (hJ : IsUnit J) {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH J) σ) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH J) {v : H} (hv : SmoothVec (lieG J) σ v), SmoothVec (lieG J) σ (σ g v) := by
  exact @UpperTheory.Lit.Bur.SmoothTranslate.smoothVec_translate
