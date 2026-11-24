module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.CoefLeftAAv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open Matrix Finset

noncomputable section

namespace AAInvW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

def OpModel : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), HInvol H →
    ∃ (M : Submodule ℂ ({x : Matrix (Fin n) (Fin n) ℂ // inUH H x} → E))
      (cls : (Matrix (Fin n) (Fin n) ℂ → E) → M) (Eh : Fin n → Fin n → Module.End ℂ M),
      GlRel Eh ∧
      (∀ (t : ℕ) (a b : Fin t → Fin n) (u : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E)
          (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUH H g),
        SmoothOnH H f → qminorOp (EabH H) a b u f g = ((qminor Eh a b u (cls f) : M) : {x : Matrix (Fin n) (Fin n) ℂ // inUH H x} → E) ⟨g, hg⟩) ∧
      ∀ s : Matrix (Fin n) (Fin n) ℂ, inUH H s → ∃ ρ : Module.End ℂ M,
        (∀ f : Matrix (Fin n) (Fin n) ℂ → E, SmoothOnH H f → cls (fun x => f (x * s)) = ρ (cls f)) ∧
        (∀ (ψ : M) (y : Matrix (Fin n) (Fin n) ℂ) (hy : inUH H y) (y' : Matrix (Fin n) (Fin n) ℂ)
            (hy' : inUH H y'), y' = y * s → ((ρ ψ : M) : {x : Matrix (Fin n) (Fin n) ℂ // inUH H x} → E) ⟨y, hy⟩ = (ψ : {x : Matrix (Fin n) (Fin n) ℂ // inUH H x} → E) ⟨y', hy'⟩) ∧
        ∀ a b : Fin n, Eh a b * ρ = ρ * ∑ c, ∑ d, (s⁻¹ c a * s b d) • Eh c d

end AAInvW
