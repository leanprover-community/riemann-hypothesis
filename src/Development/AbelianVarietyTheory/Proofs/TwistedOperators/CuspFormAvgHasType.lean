module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFinCuspAvgType

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.TypeSum GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined

variable {n : ℕ}

theorem mul_inv_mem_UH {G G₀ A B : Mx n} (hB : IsUnit B) (hA : Aᴴ * G * A = G₀) (hB' : Bᴴ * G * B = G₀) :
    A * B⁻¹ ∈ Formalism.QuantumDeterminants.UH G := by
  have h := Matrix.mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hB)
  show (A * B⁻¹)ᴴ * G * (A * B⁻¹) = G
  calc (A * B⁻¹)ᴴ * G * (A * B⁻¹) = (B⁻¹)ᴴ * (Aᴴ * G * A) * B⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (B * B⁻¹)ᴴ * G * (B * B⁻¹) := by rw [hA, ← hB']; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by rw [h]; simp

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool} {σ : Mx n → (H →L[ℂ] H)}

def uIso (hσ : IsURepOn (UJset ε) σ) {a b : Mx n} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) (hab : a * b = 1)
    (hba : b * a = 1) : H ≃ₗᵢ[ℂ] H :=
  { toFun := σ a
    invFun := σ b
    map_add' := map_add _
    map_smul' := map_smul _
    left_inv := fun w => by
      show σ b (σ a w) = w
      rw [← sigma_mul hσ hb ha, hba, sigma_one hσ]
    right_inv := fun w => by
      show σ a (σ b w) = w
      rw [← sigma_mul hσ ha hb, hab, sigma_one hσ]
    norm_map' := hσ.2.1 a ha }

theorem uIso_apply (hσ : IsURepOn (UJset ε) σ) {a b : Mx n} (ha : a ∈ UJset ε) (hb : b ∈ UJset ε) (hab : a * b = 1)
    (hba : b * a = 1) (w : H) : uIso hσ ha hb hab hba w = σ a w := rfl

end GlobalTheory.KFinCuspAvgType

end

namespace GlobalTheory.KFinCuspAvgType

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.TypeSum GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined

end GlobalTheory.KFinCuspAvgType
