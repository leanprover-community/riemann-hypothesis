module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open UpperTheory.Gal.Int.Geo
open CategoryTheory AlgebraicGeometry

private theorem powMap_congr {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f f' : S' ⟶ S} {φ φ' : A'.left ⟶ A.left}
    (hf : f = f') (hφ : φ = φ') (h : φ ≫ A.hom = A'.hom ≫ f) (h' : φ' ≫ A.hom = A'.hom ≫ f') (k : ℕ) :
    GlobalTheory.KS.powMap f φ h k = GlobalTheory.KS.powMap f' φ' h' k := by
  subst hf hφ
  rfl

theorem UpperTheory.tower_invariant_of_base_invariant_powerCartesian :
    BaseInv → PowCart → PiInv := by
  intro hB hP p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hK N' N t c a hN hNum C' C u hu x y
  obtain ⟨π, o, ψ, φ, hw, ov, tr, e⟩ := T.tr_eq N' N u x y
  obtain ⟨h1, h2⟩ := hB p D G L E gb w q r 𝔴 𝔫 S k T K₀ hK N' N t c a hN hNum C' C u hu
    ⟨π, o, ψ, φ, ov, tr⟩
  have h1' : π ≫ C.j = C'.j := h1
  have h2' : (ψ.left ≫ φ.φ) ≫ C.m.φ = C'.m.φ := by
    rw [Category.assoc]; exact h2
  have hv := C.m.cart.1.w
  have hw' : ((ψ.left ≫ φ.φ) ≫ C.m.φ) ≫ S.Y.univ.A.hom = (T.M N').univ.A.hom ≫ π ≫ C.j := by
    rw [Category.assoc, hv, ← Category.assoc, hw, Category.assoc]
  have hc := (hP _ _ _ (T.M N').univ.A (T.M N).univ.A S.Y.univ.A π C.j (ψ.left ≫ φ.φ) C.m.φ hw hv k).2.2 hw'
  simp only [Site.pi, Cls.pw]
  rw [← Category.assoc, e, Category.assoc, hc]
  exact congrArg _ (powMap_congr h1' h2' _ _ k)
