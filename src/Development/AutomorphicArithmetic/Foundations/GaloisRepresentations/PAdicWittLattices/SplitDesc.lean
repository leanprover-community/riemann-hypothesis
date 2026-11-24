module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.BcMapFst
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV

namespace UpperTheory.Gal.G3

def SplitDesc : Prop := ∀ {Z Y W : Scheme.{0}} (s : Y ⟶ Z) (c : W ⟶ Z) [IsFinite c] [Etale c] [Surjective c] (J : Type) [Finite J]
  (σ : J → (W ⟶ Y)), Splits s c σ → IsFinite s ∧ Etale s

def CharVan : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k], (l : k) = 0 → ∀ {X : Scheme.{0}} (_ : X ⟶ sp k) (n i : ℤ),
  Subsingleton (Hl l (sch.obj X) n i)

def CorrUniq : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] {Z Y Z' : Scheme.{0}} (_ : Z ⟶ sp k) (s : Y ⟶ Z) (t : Y ⟶ Z')
  (A A' : Htot l (sch.obj Z') →ₗ[ℚ_[l]] Htot l (sch.obj Z)), IsCorrOp l s t A → IsCorrOp l s t A' → A = A'

def VBcS : Prop := ∀ (l : ℕ) [Fact l.Prime] (k Ω : Type) [Field k] [IsAlgClosed k] [Field Ω] [IsAlgClosed Ω] (φ : k →+* Ω),
  IsUnit (l : k) → ∀ {X : Scheme.{0}} (p : X ⟶ sp k) [IsProper p] [Smooth p] (n i : ℤ),
  Function.Bijective (pullHQ l (sch.map (pullback.fst p (Spec.map (CommRingCat.ofHom φ)))) n i)

end UpperTheory.Gal.G3

end
