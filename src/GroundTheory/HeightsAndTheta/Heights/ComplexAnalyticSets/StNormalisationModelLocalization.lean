module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationLength
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModel
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def normalModelSubmonoid {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (q : Fin n → ℂ) : Submonoid (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) :=
  (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl.map
    ((Ideal.Quotient.mk M.ideal).comp
      (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ).toRingHom)

theorem mk_rename_mem_normalModelSubmonoid {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J) (q : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) (hf : eval q f ≠ 0) :
    Ideal.Quotient.mk M.ideal (rename Sum.inl f) ∈ normalModelSubmonoid M q :=
  Submonoid.mem_map_of_mem _ (show f ∈ (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).primeCompl from
    fun h ↦ hf (RingHom.mem_ker.1 h))

theorem zero_not_mem_normalModelSubmonoid {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J) (q : Fin n → ℂ) (hq : q ∈ zeroSet J) :
    (0 : MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) ∉ normalModelSubmonoid M q := by
  rintro ⟨f, hf, h0⟩
  apply hf
  refine RingHom.mem_ker.2 (hq f ?_)
  rw [← M.comap_eq, Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
  exact h0

def NormalisationModelLocalization.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J),
    J.IsPrime →
      ∃ e : curveNormalisation J q ≃+* Localization (normalModelSubmonoid M q),
        ∀ f : MvPolynomial (Fin n) ℂ,
          e (algebraMap (curveLocalRing J q) (curveNormalisation J q)
              (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing J q) f)) =
            algebraMap (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) (Localization (normalModelSubmonoid M q))
              (Ideal.Quotient.mk M.ideal (rename Sum.inl f))

end

end GroundTheory.Heights₂.Heights
