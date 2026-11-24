module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalDomainMassOneCocompactLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageOfIsCuspForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageMapLatticeEquiv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetIntegralFundamentalDomainEqMassMulAverage
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.RSJ GlobalTheory.MirTower GlobalTheory.CuspGeneric Formalism.L2.Host
open scoped ENNReal NNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.JSW.SpanProps

theorem avg_eq_zero {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {F : GA E a → ℂ}
    (hcont : Continuous F) (hleft : ∀ γ g, F (ratGL E a γ * g) = F g) (hc : IsCuspidal F)
    (r : ℕ) (hr : 0 < r) (hra : r ≤ a - 1) (g : GA E a) :
    avg (ratV E (UnipotentBlockColumnIndex a r (a - 1))) (fun x => F (blkU x * g)) = 0 := by
  have hra' : r < a := by omega
  have hper := per_blk (E := E) (r := r) (m := a - 1) hcont (fun c g => hleft _ g) g
  have hper2 : Per (ratN E a r) (fun x => F (blkU (blkIxHomeo r x) * g)) :=
    ⟨hper.1.comp (blkIxHomeo r).continuous, fun γ hγ x => by
      simp only [map_add (f := _)]
      exact hper.2 _ ((blkIxHomeo_mem r γ).2 hγ) _⟩
  have key := _root_.GlobalTheory.CuspGeneric.avg_equiv _ _ (ratN E a r) (ratV E _) (isCoLat_ratV E (BlockIx a r))
    (isCoLat_ratV E _) (blkIxHomeo r) (blkIxHomeo_mem r) _ hper
  rw [← key]
  have hfun : (fun x => F (blkU (blkIxHomeo r x) * g)) = fun x => F (unip x * g) :=
    funext fun x => by rw [← blkU_comp_equiv]; rfl
  rw [hfun] at hper2 ⊢
  letI : MeasurableSpace (BlockIx a r → Ad E) := borel _
  haveI : BorelSpace (BlockIx a r → Ad E) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, hF, h1⟩ := _root_.GlobalTheory.CuspGeneric.exists_fundamentalDomain_mass_one _ (ratN E a r) (isCoLat_ratV E (BlockIx a r))
  obtain ⟨-, -, -, hint⟩ := _root_.GlobalTheory.CuspGeneric.setIntegral_eq_mass_mul_avg _ _ (isCoLat_ratV E (BlockIx a r)) μ 𝓕 hμ hF _ hper2
  have hc' := hc r hr hra' μ 𝓕 hμ hF g
  rw [hint, h1] at hc'
  simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul] at hc'
  exact hc'

end GlobalTheory.JSW.SpanProps

theorem GlobalTheory.JSW.mspanR_cont_left_avg : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (π : CuspSub E (m + 1))
    (ω : HChar E), ω.IsUnitary → π.HasCentChar ω → ∀ φ ∈ GlobalTheory.JSW.mspanR π, Continuous φ ∧
    (∀ γ g, φ (ratGL E (m + 1) γ * g) = φ g) ∧
    ∀ r, 0 < r → r ≤ m → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (m + 1) r m)) (fun x => φ (blkU x * g)) = 0 := by
  intro E _ _ _ m π ω hω hc F hF
  have hπ : π.IsUnitary := ⟨ω, hω, CuspSub.hasCentral_iff.2 hc⟩
  obtain ⟨ψ, rfl, h⟩ := GlobalTheory.JSW.mspanR_words GlobalTheory.CuspOrth.cuspFormsBounded hπ F hF
  have h0 := (h []).2
  rw [GlobalTheory.JSW.word_nil] at h0
  refine ⟨h0.cont, h0.left, fun r hr hrm g => ?_⟩
  exact GlobalTheory.JSW.SpanProps.avg_eq_zero (a := m + 1) h0.cont h0.left h0.cusp r hr hrm g
