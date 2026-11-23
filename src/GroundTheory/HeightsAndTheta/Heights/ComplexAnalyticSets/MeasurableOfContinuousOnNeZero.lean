module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.EqZeroOfMemZeroLocusLineOriginIdeal
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PAffineChartTrdeg
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartDehomog
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.ENatToNat
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

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Filter Topology Matrix

noncomputable section

theorem le_ringKrullDim_slice {n e : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ : Fin n → ℂ}
    (hJ : IsAffVariety J (e + 1)) (hH : IsHomogIdeal J) (hℓ : linForm ℓ ∉ J) :
    ((e : ℕ) : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {linForm ℓ - 1})) := by
  have hP := hJ.isPrime
  have hne : J ⊔ Ideal.span {linForm ℓ - 1} ≠ ⊤ := by
    intro htop
    have h1 : (1 : MvPolynomial (Fin n) ℂ) ∈ J :=
      GroundTheory.Heights₂.Heights.ChartDehomog.proof ℂ n J ℓ 1 0 hP hH hℓ (isHomogeneous_one _ _)
        (htop ▸ Submodule.mem_top)
    exact hP.ne_top ((Ideal.eq_top_iff_one J).mpr h1)
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hne
  have hpP : p.IsPrime := hp.1.1
  have hJp : J ≤ p := le_sup_left.trans hp.1.2
  have hht := Ideal.map_height_le_one_of_mem_minimalPrimes hp
  have hpm : (p.map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient (k := ℂ)
    (p.map (Ideal.Quotient.mk J))
  rw [hJ.dim, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hJp)] at hform
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) ≤
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {linForm ℓ - 1})) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hp.1.2)
      (Ideal.Quotient.factor_surjective hp.1.2)
  refine le_trans ?_ hle
  have key : ∀ a b : ℕ∞, a ≤ 1 → a + b = ((e + 1 : ℕ) : ℕ∞) → (e : ℕ∞) ≤ b := by
    intro a b ha hab
    induction b using ENat.recTopCoe with
    | top => exact le_top
    | coe m =>
      induction a using ENat.recTopCoe with
      | top => simp at ha
      | coe k =>
        have h1 : k ≤ 1 := by exact_mod_cast ha
        have h2 : k + m = e + 1 := by exact_mod_cast hab
        exact_mod_cast (by omega : e ≤ m)
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) = D at hform ⊢
  induction D using WithBot.recBotCoe with
  | bot =>
    exfalso
    rw [WithBot.add_bot] at hform
    exact WithBot.bot_ne_coe hform
  | coe b =>
    have hab : (p.map (Ideal.Quotient.mk J)).height + b = ((e + 1 : ℕ) : ℕ∞) := by
      exact_mod_cast hform
    exact_mod_cast key _ b hht hab

theorem exists_isChowForm_iff {n e : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : IsProjPrime J) :
    (∃ F : MvPolynomial (Fin (e + 1) × Fin n) ℂ, IsChowForm J (e + 1) F) ↔
      IsAffVariety J (e + 1) :=
  ⟨fun ⟨F, hF⟩ => ⟨hJ.isPrime, GroundTheory.Heights₂.Heights.ConeDimOfChowForm.of_affineChartTrdeg
      GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof ℂ n (e + 1) J F hJ hF⟩,
    fun hA => GroundTheory.Heights₂.Heights.ChowFormExists.of_affineChartTrdeg
      GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof ℂ n (e + 1) J hJ hA.dim⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
