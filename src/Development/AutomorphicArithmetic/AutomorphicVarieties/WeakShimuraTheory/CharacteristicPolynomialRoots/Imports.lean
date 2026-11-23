module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CharacteristicPolynomialRoots.LeKerPt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuArith
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.ResLeCont
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC Formalism.MainNotions.N ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.Pu.arith :
    GlobalTheory.Published.GlobalArtinReciprocity → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (φ : B.B →ₐ[c'.O] X.B) (y : X.A →ₐ[c'.O] PadicAlgCl l), D.Good → K.IsPhi X 0 B φ →
      T.Wts (fun i => 2 * D.wts4 i) (X.P.map (y : X.A →+* PadicAlgCl l)) → ∃ w : K.s.Wt 4, (Link.pt φ y).Arith w := by
  intro hA Ω _ _ _ l _ c D T c' h K X B φ y hD hφ hW
  have he := hD.two_le
  refine auArith hA D T c' h K X B φ hφ y (Link.pt φ y) (fun b => rfl) (fun v i => Pt.psi_cont _ v i)
    (fun i => (D.wts4 i : ℤ)) ?_ hW
  rw [Fin.strictAnti_iff_succ_lt]
  intro i
  fin_cases i <;> simp [Raw.wts4]
  all_goals omega
