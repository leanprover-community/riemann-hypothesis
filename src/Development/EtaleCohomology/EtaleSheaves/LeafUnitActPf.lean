module

public import Development.EtaleCohomology.EtaleSheaves.LeafUnitPairGPf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitActPf
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafUnitPairGPf

def LeafActSheaf : Prop := ∀ (q : ℕ) [NeZero q], ∃ L : ∀ (F : Shv (ZMod q)) (U : Scheme.{0}),
    Sec (tw q 0) U →ₗ[ULift.{1} (ZMod q)] Sec F U →ₗ[ULift.{1} (ZMod q)] Sec F U,
  (∀ (F : Shv (ZMod q)) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec (tw q 0) U) (b : Sec F U),
      Sec.res g (L F U a b) = L F V (Sec.res g a) (Sec.res g b)) ∧
  (∀ {F G : Shv (ZMod q)} (φ : F ⟶ G) (U : Scheme.{0}) (a : Sec (tw q 0) U) (b : Sec F U),
      Sec.map φ (L F U a b) = L G U a (Sec.map φ b)) ∧
  ∀ (F : Shv (ZMod q)) (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (b : Sec F U), L F U (twGen 0 ζ) b = b

theorem LeafUnitAct_of (h : LeafActSheaf) : LeafUnitAct := by
  intro q _ i
  obtain ⟨L, hU, hF, hζ⟩ := h q
  refine ⟨fun U t => L ((res _ (tw q i)).X t) U, ⟨fun g t a b => hU _ g a b, fun U t a b => hF _ U a b⟩,
    fun U t ζ b => hζ _ U ζ b⟩

end LateralTheory.E.LeafUnitActPf
