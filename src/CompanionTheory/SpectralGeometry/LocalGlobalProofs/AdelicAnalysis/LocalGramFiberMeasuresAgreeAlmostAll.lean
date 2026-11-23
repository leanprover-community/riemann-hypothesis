module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresChangeOfFormStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMeasureProdOfAddGroupsStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianFormsIntegrallyEquivalentAlmostAllStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalLatticeCompactOpenUnitVolumeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem lattice_mass_fibre_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (J' : Matrix (Fin M) (Fin M) E), IsHermND σ J' → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ n : ℕ, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam, IsStdV v lam → ∀ m m', IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m → IsGramFib (Fv F v) σ J' n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m' → ∀ S, m S (latV b v) = m' S (latV b v) := by
  intro F E _ _ _ _ _ σ hσ M J hJ J' hJ' d b n
  filter_upwards [GlobalTheory.T.hermitian_forms_integrally_equivalent_almost_all F E σ hσ M J hJ J' hJ' d b] with v hv
  intro lam hlam m m' hm hm' S
  obtain ⟨g, hg, hlat⟩ := hv
  have hL := GlobalTheory.T.completion_is_local_ring F v
  obtain ⟨h1, h2, h3, h4, -⟩ := id hL
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 n M
  haveI := hlam.1
  obtain ⟨-, c2, c3⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Fv F v) d b lam hlam.1
  haveI := c2 n M
  obtain ⟨a1, a2, a3, -⟩ := GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hσ d b n M v
  have hcont : ∀ k : GL (Fin M) (Fv F v ⊗[F] E),
      Continuous (actTup (Fv F v) (n := n) k) := by
    intro k
    refine continuous_pi fun a => ?_
    exact Continuous.matrix_mulVec continuous_const ((continuous_apply a))
  have hinv : ∀ (k l : GL (Fin M) (Fv F v ⊗[F] E)), k * l = 1 → ∀ X : Fin n → Fin M → Fv F v ⊗[F] E,
      actTup (Fv F v) k (actTup (Fv F v) l X) = X := by
    intro k l hkl X
    funext a
    have h : (k : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) * (l : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) = 1 := by
      rw [← Units.val_mul, hkl, Units.val_one]
    simp only [actTup, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  let e : (Fin n → Fin M → Fv F v ⊗[F] E) ≃+ (Fin n → Fin M → Fv F v ⊗[F] E) :=
    { toFun := actTup (Fv F v) g
      invFun := actTup (Fv F v) g⁻¹
      left_inv := hinv g⁻¹ g (inv_mul_cancel g)
      right_inv := hinv g g⁻¹ (mul_inv_cancel g)
      map_add' := by
        intro X Y
        funext a
        simp only [actTup, Pi.add_apply, Matrix.mulVec_add] }
  have hmap : (coordW (Fv F v) b lam n M).map e = coordW (Fv F v) b lam n M :=
    (GlobalTheory.T.map_addHaar_addEquiv_eq_smul_and_eq_of_compact_open _ _ (coordW (Fv F v) b lam n M) (coordW (Fv F v) b lam n M) e (hcont g)
      (hcont g⁻¹)).2 (latV b v) (latV b v) a1 a2 ⟨0, a3⟩ (hlat n) rfl
  have hfib := GlobalTheory.T.gram_fiber_measures_change_of_form F E σ hσ M J hJ J' hJ' (Fv F v) hL n (coordW (Fv F v) b lam n M)
    (coordHerm (Fv F v) σ b lam n) m (c2 n M) (c3 n) hm (coordW (Fv F v) b lam n M) m' (c2 n M) hm' g hg 1
    (by rw [one_smul]; exact hmap) S
  have hval := congrArg (fun μ => μ (latV b v)) hfib
  simp only [one_smul] at hval
  rw [Measure.map_apply (hcont g).measurable a2.measurableSet] at hval
  have hpre : actTup (Fv F v) (n := n) g ⁻¹' latV (M := M) (n := n) b v = latV b v := by
    ext X
    exact hlat n X
  rw [hpre] at hval
  exact hval.symm

end GlobalTheory.CompanionTheory.SW
