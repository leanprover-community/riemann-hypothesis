module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct

namespace GlobalTheory.Published

def MinguezThetaGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n m : ℕ), 1 ≤ n → 1 ≤ m →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin n) k) W), IsSmooth π → π.IsIrreducible →
    (∃ f : SB (Matrix (Fin n) (Fin m) k) →ₗ[ℂ] W, f ≠ 0 ∧ ∀ (h : GL (Fin n) k) (Φ Φ' : SB (Matrix (Fin n) (Fin m) k)),
      (Φ' : Matrix (Fin n) (Fin m) k → ℂ) = om 1 (1 : GL (Fin m) k) h Φ → f Φ' = π h (f Φ)) →
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (π' : Representation ℂ (GL (Fin m) k) V),
      IsSmooth π' ∧ π'.IsIrreducible ∧ OmQuot 1 π' π ∧
      (∀ (V' : Type) [AddCommGroup V'] [Module ℂ V'] (π'' : Representation ℂ (GL (Fin m) k) V'),
        IsSmooth π'' → π''.IsIrreducible → OmQuot 1 π'' π → Nonempty (π''.Equiv π')) ∧
      ∀ f f' : SB (Matrix (Fin n) (Fin m) k) →ₗ[ℂ] V ⊗[ℂ] W,
        (∀ F ∈ ({f, f'} : Set (SB (Matrix (Fin n) (Fin m) k) →ₗ[ℂ] V ⊗[ℂ] W)),
          ∀ (g : GL (Fin m) k) (h : GL (Fin n) k) (Φ Φ' : SB (Matrix (Fin n) (Fin m) k)),
            (Φ' : Matrix (Fin n) (Fin m) k → ℂ) = om 1 g h Φ → F Φ' = TensorProduct.map (π' g) (π h) (F Φ)) →
        f ≠ 0 → ∃ c : ℂ, f' = c • f

namespace MinguezThetaGL

end MinguezThetaGL

end GlobalTheory.Published
