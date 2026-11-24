module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVecUnitaryModule
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorOnUnitaryCoefficientEqDerived
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.CoefWord

theorem eword_coef : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (v : GlobalTheory.SmoothVecMod.smoothVec ε σ) (w : H) (l : List (Fin n × Fin n)), ∀ g ∈ Formalism.MainNotions.S.UJset ε, Formalism.REAL.Eword ε l (fun x => ⟪w, σ x (v : H)⟫_ℂ) g = ⟪w, σ g (((l.map fun ab => GlobalTheory.SmoothVecMod.unitAct hσ ab.1 ab.2).prod v : GlobalTheory.SmoothVecMod.smoothVec ε σ) : H)⟫_ℂ := by
  intro n ε H _ _ σ hσ v w l
  induction l with
  | nil =>
    intro g _
    rfl
  | cons p l ih =>
    intro g hg
    have hg' : Formalism.REAL.inUJ ε g := hg
    set u : GlobalTheory.SmoothVecMod.smoothVec ε σ :=
      (l.map fun ab => GlobalTheory.SmoothVecMod.unitAct hσ ab.1 ab.2).prod v with hu
    have h1 : Formalism.REAL.Eword ε (p :: l) (fun x => ⟪w, σ x (v : H)⟫_ℂ) g =
        Formalism.REAL.EabV ε p.1 p.2 (Formalism.REAL.Eword ε l (fun x => ⟪w, σ x (v : H)⟫_ℂ)) g := rfl
    have h2 : Formalism.REAL.EabV ε p.1 p.2 (Formalism.REAL.Eword ε l (fun x => ⟪w, σ x (v : H)⟫_ℂ)) g =
        Formalism.REAL.EabV ε p.1 p.2 (fun x => innerSL ℂ w (σ x (u : H))) g :=
      GlobalTheory.SmoothVecMod.eabV_congr (fun x hx => ih x hx) p.1 p.2 hg'
    have h3 := GlobalTheory.CapelliCoef.eabV_pair (innerSL ℂ w) (f := fun x => σ x (u : H)) u.2 p.1 p.2 hg'
    have h4 := GlobalTheory.SmoothVecMod.rep_eabV hσ u.2 p.1 p.2 hg'
    rw [h1, h2, ← h3, ← h4]
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rfl

end GlobalTheory.CompanionTheory.CoefWord
