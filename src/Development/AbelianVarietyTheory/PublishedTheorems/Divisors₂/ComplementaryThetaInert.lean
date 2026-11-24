module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.Published

def ComplementaryThetaInert : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n a a' r : ℕ) (V : Spc F E a) (V' : Spc F E a') (W : Spc F E (a + a')) (M : Model σ V W) (M' : Model σ V' W)
      (ψ : AddChar (AF F) ℂ) (χV χW χV' χW' : Chr F E) (om : Rep σ V W) (om' : Rep σ V' W),
      a + a' = 2 * n → a = a' + 2 * r → 0 < r → 0 < a' → IsStd ψ →
      (∀ i j, σ (V.J j i) = V.J i j) → V.J.det ≠ 0 → (∀ i j, σ (V'.J j i) = V'.J i j) → V'.J.det ≠ 0 →
      (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χV a →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χV' a' →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW (a + a') →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW' (a + a') →
      IsHecke F E χV → IsHecke F E χV' → IsHecke F E χW → IsHecke F E χW' →
      M.IsWeil ψ χV χW om → M'.IsWeil ψ χV' χW' om' →
    ∀ v : Pl (F := F), IsField (Fv F v ⊗[F] E) →
      (∃ Cy : Matrix (Fin (a + a')) (Fin n) (Fv F v ⊗[F] E),
        IsLagr (Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ) (JR (Fv F v) W.J) Cy) →
      (∃ P : Matrix (Fin a) (Fin a' ⊕ (Fin r ⊕ Fin r)) (Fv F v ⊗[F] E),
        Pᵀ * JR (F := F) (Fv F v) V.J * P.map (sigR (Fv F v) σ) =
          (Matrix.fromBlocks (JR (Fv F v) V'.J) 0 0 (Matrix.fromBlocks 0 1 1 0) :
            Matrix (Fin a' ⊕ (Fin r ⊕ Fin r)) (Fin a' ⊕ (Fin r ⊕ Fin r)) (Fv F v ⊗[F] E))) →
      (∀ z : (AE F E)ˣ, At (evFin F v) ((z : AE F E) - 1) → χV z = χV' z ∧ χW z = 1 ∧ χW' z = 1) →
      augAt om' v ≠ SB _ ∧
      (∀ N : Submodule ℂ (_ → ℂ), augAt om' v ≤ N → N ≤ SB _ → (∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ N, ∀ φ₁ ∈ SB _,
        Acts (evFin F v) (om' (1, h)) φ φ₁ → φ₁ ∈ N) → N = augAt om' v ∨ N = SB _) ∧
      ∃ p : ((Fin a × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (((Fin a' × Fin (a + a') → Fv F v) → ℂ) ⧸ augAt om' v),
        (SB _).map p = (SB _).map (augAt om' v).mkQ ∧ augAt om v ≤ LinearMap.ker p ∧
        ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _, ∀ φ' ∈ SB _, ∀ φ₁ ∈ SB _, ∀ φ₁' ∈ SB _,
          Acts (evFin F v) (om (1, h)) φ φ₁ → Acts (evFin F v) (om' (1, h)) φ' φ₁' →
          p φ = (augAt om' v).mkQ φ' → p φ₁ = (augAt om' v).mkQ φ₁'

end GlobalTheory.Published

end
