module

public import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Valuation.ValuationSubring
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

@[expose] public section

noncomputable section

open scoped MatrixGroups
open Matrix

namespace GlobalTheory.KZ.ES

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def Lev (X : Tower Ω ε) (M : ℕ) (f : X.K) : Prop :=
  ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f

def IntC (X : Tower Ω ε) (V : ValuationSubring Ω) (f : X.K) : Prop := ∀ r : ℚ, (X.exp f).coeff r ∈ V

def SmallC (X : Tower Ω ε) (V : ValuationSubring Ω) (f : X.K) : Prop := ∀ r : ℚ, (X.exp f).coeff r ∈ V.nonunits

def Prim (X : Tower Ω ε) (V : ValuationSubring Ω) (f : X.K) : Prop :=
  IntC X V f ∧ ∃ r : ℚ, V.valuation ((X.exp f).coeff r) = 1

def Dom (X : Tower Ω ε) (V : ValuationSubring Ω) (W : ValuationSubring X.K) : Prop :=
  (∀ f, IntC X V f → f ∈ W) ∧ (∀ f, SmallC X V f → W.valuation f < 1) ∧ ∀ f, Prim X V f → W.valuation f = 1

def Gauss {F L : Type} [Field F] [Field L] [Algebra F L] (t : L) (V : ValuationSubring F) (W : ValuationSubring L) : Prop :=
  (∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V) ∧ ∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) →
    (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W.valuation (Polynomial.aeval t P) = 1

def FrobV (V : ValuationSubring Ω) (q : ℕ) (s : Ω ≃ₐ[ℚ] Ω) : Prop :=
  ((q : ℕ) : Ω) ∈ V.nonunits ∧ ∀ x ∈ V, s x ∈ V ∧ s.symm x ∈ V ∧ V.valuation (s x - x ^ q) < 1

def Nq (X : Tower Ω ε) (M q : ℕ) (f : X.K) : X.K :=
  ∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f

def DiagMod (M q : ℕ) (γ : SL(2, ℤ)) : Prop :=
  (en γ 0 1 : ZMod M) = 0 ∧ (en γ 1 0 : ZMod M) = 0 ∧ (en γ 1 1 : ZMod M) = q

def levF (X : Tower Ω ε) (M : ℕ) : IntermediateField Ω (AlgebraicClosure X.K) :=
  IntermediateField.adjoin Ω (algebraMap X.K (AlgebraicClosure X.K) '' {f | Lev X M f})

def rootF (X : Tower Ω ε) (M₀ M m : ℕ) (U : X.K) : IntermediateField (levF X M₀) (AlgebraicClosure X.K) :=
  IntermediateField.adjoin (levF X M₀) (algebraMap X.K (AlgebraicClosure X.K) '' {f | Lev X M f} ∪
    {y | ∃ γ ∈ CongruenceSubgroup.Gamma M₀, y ^ m = algebraMap X.K (AlgebraicClosure X.K) (X.sl (ofSL γ) U)})

theorem lev_jK (X : Tower Ω ε) (M : ℕ) : Lev X M X.jK := fun γ _ => X.j_inv γ

end GlobalTheory.KZ.ES
