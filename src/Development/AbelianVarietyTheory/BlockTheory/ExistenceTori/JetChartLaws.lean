module

public import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
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
import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {X₀ : Scheme.{0}} {S : Type} [CommRing S]

abbrev algO (x : Sp S ⟶ X₀) (B : Type) [CommRing B] [Algebra S B] : Over X₀ :=
  Over.mk (spMap (algebraMap S B) ≫ x)

def algMap (x : Sp S ⟶ X₀) {B B' : Type} [CommRing B] [Algebra S B] [CommRing B'] [Algebra S B']
    (f : B →ₐ[S] B') : algO x B' ⟶ algO x B :=
  Over.homMk (spMap (f : B →+* B')) (by
    change spMap (f : B →+* B') ≫ spMap (algebraMap S B) ≫ x = spMap (algebraMap S B') ≫ x
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap])

def jetVec {σ : Type} (c : σ → S) : Jet S σ 1 →ₐ[S] DualNumber S :=
  liftJet (MvPolynomial.aeval fun i => c i • (DualNumber.eps : DualNumber S)) (by
    apply le_bot_iff.1
    have h1 : Ideal.span (Set.range fun i =>
        (MvPolynomial.aeval fun i => c i • (DualNumber.eps : DualNumber S))
          (MvPolynomial.X i : MvPolynomial σ S)) ≤ Ideal.span {(DualNumber.eps : DualNumber S)} := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp only [MvPolynomial.aeval_X, Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    refine (Ideal.pow_right_mono h1 _).trans ?_
    rw [Ideal.span_singleton_pow]
    simp)

abbrev JetPts (G : Over X₀) (x : Sp S ⟶ X₀) (d : ℕ) : Type :=
  ∀ m : ℕ, algO x (Jet S (Fin d) m) ⟶ G

section Group

variable (G : Over X₀) [GrpObj G] (x : Sp S ⟶ X₀) {d : ℕ}

def IsFormalParam (j : JetPts G x d) : Prop :=
  (∀ m, algMap x (jetTrunc : Jet S (Fin d) (m + 1) →ₐ[S] Jet S (Fin d) m) ≫ j (m + 1) = j m) ∧
  (∀ m, algMap x (jetAug : Jet S (Fin d) m →ₐ[S] S) ≫ j m = 1) ∧
  ∀ (m : ℕ) (B : Type) [CommRing B] [Algebra S B] (I : Ideal B), I ^ (m + 1) = ⊥ →
    ∀ g : algO x B ⟶ G, algMap x (Ideal.Quotient.mkₐ S I) ≫ g = 1 →
      ∃! f : Jet S (Fin d) m →ₐ[S] B, algMap x f ≫ j m = g



omit [GrpObj G] in
def TanIs (j : JetPts G x d) (v : Sp (DualNumber S) ⟶ G.left) (c : Fin d → S) : Prop :=
  v = (algMap x (jetVec c) ≫ j 1).left

end Group

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem jetVec_X {σ : Type} (c : σ → S) (i : σ) :
    jetVec c (Ideal.Quotient.mk _ (MvPolynomial.X i)) = c i • (DualNumber.eps : DualNumber S) := by
  have h : jetVec c (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      MvPolynomial.aeval (R := S) (fun i => c i • (DualNumber.eps : DualNumber S)) (MvPolynomial.X i) := rfl
  rw [h, MvPolynomial.aeval_X]

end GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws
