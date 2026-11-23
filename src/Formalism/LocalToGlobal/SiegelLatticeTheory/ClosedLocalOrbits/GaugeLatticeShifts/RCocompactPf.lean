module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipBasis
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

namespace Formalism.L2.SG.TermOp.Vanish

open Formalism.L2.SG.Full

def Gr {D : D7} (X : HidaSetting D) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) :
    Matrix (Kap X) (Kap X) X.B.I.E :=
  Bm' X * M * Bm X

def RatApprox : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (M : GL (Fin X.B.I.n) X.B.I.E), M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J →
    ∀ k : ℕ, 1 ≤ k → ∀ d : ℕ, 1 ≤ d → ∃ C : ℝ, ∀ P : InfinitePlace X.B.I.F → Matrix (Kap X) (Kap X) ℂ,
      (∀ v, InPat (lvk X) k (P v) ∧
        InPat (lvk X) 1 ((Gr X (↑M⁻¹ : Matrix _ _ _)).map (X.B.I.φ v) * P v * (Gr X (M : Matrix _ _ _)).map (X.B.I.φ v)) ∧
        (P v)ᴴ * JBv X v = -(JBv X v * P v)) →
      ∃ Y : Matrix (Kap X) (Kap X) X.B.I.E, InPat (lvk X) k Y ∧
        InPat (lvk X) 1 (Gr X (↑M⁻¹ : Matrix _ _ _) * Y * Gr X (M : Matrix _ _ _)) ∧ Yᴴ * JB X = -(JB X * Y) ∧
        (∃ A : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E), Y = (d : X.B.I.E) • A.map (fun a => (a : X.B.I.E))) ∧
        ∀ v i j, ‖(Y.map (X.B.I.φ v) - P v) i j‖ ≤ C

def RatMem : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (M : GL (Fin X.B.I.n) X.B.I.E),
    M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J → (∀ y, X.crd (t.lin y) = (M : Matrix _ _ _) *ᵥ X.crd y) →
    ∃ d : ℕ, 1 ≤ d ∧ ∀ Z : Matrix (Kap X) (Kap X) X.B.I.E, InPat (lvk X) 1 Z →
      InPat (lvk X) 1 (Gr X (↑M⁻¹ : Matrix _ _ _) * Z * Gr X (M : Matrix _ _ _)) → Zᴴ * JB X = -(JB X * Z) →
      (∃ A : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E), Z = (d : X.B.I.E) • A.map (fun a => (a : X.B.I.E))) →
      ∃ s ∈ ROinf t, ∀ v, Mv X v s = (cay (2 * D.R.rS + 2) Z).map (X.B.I.φ v)

end Formalism.L2.SG.TermOp.Vanish
