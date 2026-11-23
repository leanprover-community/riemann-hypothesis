module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftVOneMul
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocModel

theorem weil_normalises_schr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (Y : Type) [AddCommGroup Y] (Xm : Y →+ Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
      (∀ y, At (evFin F v) (Xm y)) →
      ∀ ρ : Y → Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v)),
      (∀ x (φ : SB (Fin a × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M.co.rho B.ψ (Xm x))
        (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) ((ρ x φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ)) →
      ∀ (Γ : Type) [Group Γ] (j : Γ →* UA σ G.V.J × UA σ G.W.J) (ω : Γ →* Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v))),
      (∀ g (φ : SB (Fin a × Fin (a + a') → Fv F v)) (φ₁ : (Fin a × Fin (a + a') → Fv F v) → ℂ),
        Acts (evFin F v) (om (j g)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          φ₁ = ((ω g φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ)) →
      ∀ actY : Γ → Y → Y, (∀ g x, actAB (cA σ) (j g) (Xm x) = Xm (actY g x)) →
      ∀ g x, ω g * ρ x = ρ (actY g x) * ω g := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v Y _ Xm hXm ρ hρ Γ _ j ω hω actY hact g x
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (F := F) (Fin a × Fin (a + a')) v
  have hS := IsUWeilPair.isUSplitting hT.weil
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  apply GlobalTheory.InertAvgDual.eq_of_tens_eq v hR0 (hR _ φ.2).1
  simp only [Module.End.mul_apply]
  have h1 := (hω g (ρ x φ) _).2 rfl R (hR _ (ρ x φ).2)
  have h2 := hρ x φ R (hR _ φ.2)
  have h3 := (hω g φ _).2 rfl R (hR _ φ.2)
  have h4 := hρ (actY g x) (ω g φ) R (hR _ (ω g φ).2)
  have h5 := hS.impl (j g) (Xm x) (tens (evFin F v) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) R) (hR _ φ.2).2
  rw [← h1, ← h4, ← h2, h5, hact, h3]

end GlobalTheory.InertLocModel
