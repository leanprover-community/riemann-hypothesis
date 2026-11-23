module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenVar
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericMemberSectionNeZeroIsPrimeAffineChart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.GenericMember
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.genericMemberSection_ne_zero_isPrime_affineChart : ∀ (k : Type) [Field k] (N : ℕ) (X X' : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp k) (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X) (L : LB X) (hL : L.IsLB) (b : Fin N → L.Sec) (V : X.Opens) (hne : (V : Set X).Nonempty) (hW : IsAffineOpen (π ⁻¹ᵁ V)) (c : L.ι) (hVc : V ≤ L.U c) (j : Fin N), IsUnit (resG X hVc ((b j).f c)) → letI : Algebra k Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ V le_top).hom.toAlgebra; ∀ e : FractionRing (MvPolynomial (Fin N) k) ⊗[k] Γ(X, V) ≃+* Γ(X', π ⁻¹ᵁ V), (∀ a, e (1 ⊗ₜ a) = (π.app V).hom a) → (∀ q, e (q ⊗ₜ 1) = ((Scheme.ΓSpecIso _).inv ≫ f'.appLE ⊤ (π ⁻¹ᵁ V) le_top).hom q) → (genSec k N f' π L b).f (fun _ => c) ≠ 0 ∧ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩ = ⊤ ∨ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩).IsPrime ∧ ((secIdeal (LB.isLB_pull hL π) (genSec k N f' π L b)).ideal ⟨π ⁻¹ᵁ V, hW⟩).comap (π.app V).hom = ⊥) := by
  first | exact @GlobalTheory.GenericMember.genSec_chart_ne_zero_and_isPrime | exact GlobalTheory.GenericMember.genSec_chart_ne_zero_and_isPrime | (intros; apply GlobalTheory.GenericMember.genSec_chart_ne_zero_and_isPrime <;> assumption)
