module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsSnapper
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Defs

variable (k : Type u) [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

def eulerCharQuot {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F₁ F₂ : SubSystem k x E) : ℤ :=
  ∑ i ∈ Finset.range (N + 1), (-1 : ℤ) ^ i * (Module.finrank k (SubSystem.quotH F₁ F₂ i) : ℤ)

def pieceChar (pp : Ideal (Poly k N)) (a : ℤ) {t : ℕ} (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ) : ℤ :=
  eulerCharQuot k
    (((twistSys k x a).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
    ((((twistSys k x a).twist (idealSys x pp)).twistPows t (fun j => (L j).toSubSystem) n).twist
      (twistSys k x c))

end Defs

def IsNumPolyLT (t D : ℕ) (f : (Fin t → ℕ) → ℤ → ℚ) : Prop :=
  ∃ Q : MvPolynomial (Fin (t + 1)) ℚ, (Q = 0 ∨ Q.totalDegree < D) ∧
    ∀ (n : Fin t → ℕ) (c : ℤ), f n c = eval (Fin.snoc (α := fun _ => ℚ) (fun j => (n j : ℚ)) (c : ℚ)) Q

end

end GroundTheory.Heights₂.Heights.Kleiman
