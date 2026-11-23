module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.Pieces
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjectionsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureTransportStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsGramFiberMeasuresStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasuresContinuityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeStableAlmostEverywhere
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryActionEulerProductStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryIsomOfIsometry
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.IsEulerProdConstIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.SWIsom
open scoped TensorProduct ENNReal NNReal Matrix

theorem isomC : IsomC := by
  intro F E _ _ _ _ _ σ hCM M J hJ g J' hJ'eq n T hT _ hSW
  subst hJ'eq
  have hJ' := isHermND_conj σ hCM J hJ g
  intro d b laminf lam hinf hlam μ 𝓕 hμ h𝓕 minf m hminf hm
  obtain ⟨⟨i1, i2, i3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := i1
  haveI := i2
  haveI := i3
  obtain ⟨e, hmat, hrat⟩ := GlobalTheory.CompanionTheory.SW.HIsom.unitaryIsom_of_isometry F E σ hCM M J hJ g _ rfl (AF F)
  obtain ⟨tg, -, -, -, bs, -⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ (AF F)
  obtain ⟨tg', -, -, -, bs', -⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M _ hJ' (AF F)
  haveI := tg
  haveI := tg'
  haveI := bs
  haveI := bs'
  haveI : μ.IsHaarMeasure := hμ
  let He := e.toHomeomorph.toMeasurableEquiv
  have hμ' : IsHaarH F E σ M _ (μ.map He.symm) := ContinuousMulEquiv.isHaarMeasure_map μ e.symm
  have hmm : (μ.map He.symm).map He = μ := by
    rw [Measure.map_map He.measurable He.symm.measurable]
    simp
  have hq : Measure.QuasiMeasurePreserving e (μ.map He.symm) μ :=
    (MeasurePreserving.mk He.measurable hmm).quasiMeasurePreserving
  have h𝓕' : IsFDH F E σ M _ (μ.map He.symm) (He ⁻¹' 𝓕) :=
    isFD_pull σ e.toMulEquiv hrat hq h𝓕
  have hLi : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  have hWi := haar_of_loc σ hCM (Ainf F) hLi b laminf hinf.1 n M
  have hWv := fun v => haar_of_loc σ hCM (Fv F v) (hLv v) b (lam v) (hlam v).1 n M
  obtain ⟨minf', hminf'⟩ := GlobalTheory.T.exists_gram_fiber_measures F E σ hCM M _ hJ' (Ainf F) hLi n _ _ hWi.1 hWi.2
  choose m' hm' using fun v =>
    GlobalTheory.T.exists_gram_fiber_measures F E σ hCM M _ hJ' (Fv F v) (hLv v) n _ _ (hWv v).1 (hWv v).2
  obtain ⟨cinf, c, hUP, hci, hcv⟩ := GlobalTheory.T.haar_modulus_gl_action_product_formula F E σ hCM n M g
  obtain ⟨κ, hEul, hκ⟩ := hSW d b laminf lam hinf hlam (μ.map He.symm) (He ⁻¹' 𝓕) hμ' h𝓕' minf' m' hminf' hm'
  refine ⟨κ, ?_, hκ⟩
  have hfin : ∀ v, (cfac E v • m v (hermOf (Fv F v) σ T hT)) (latV b v) < ⊤ := by
    intro v
    haveI := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hCM M J hJ (Fv F v) (hLv v) n _ _ (m v) (hWv v).1 (hWv v).2 (hm v)
      (hermOf (Fv F v) σ T hT)).1
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top
      ((GlobalTheory.T.adelic_tuple_projections F E σ hCM d b n M).2.2.2.1 v).1.measure_lt_top
  have hproj : ∀ X : Fin n → Fin M → AF F ⊗[F] E,
      projInf (actTup (AF F) (bc (inclR (AF F)) g) X) =
          actTup (Ainf F) (bc (inclR (Ainf F)) g) (projInf X) ∧
        ∀ v, projV v (projFin (actTup (AF F) (bc (inclR (AF F)) g) X)) =
          actTup (Fv F v) (bc (inclR (Fv F v)) g) (projV v (projFin X)) := by
    intro X
    refine ⟨?_, fun v => ?_⟩
    · funext a i
      exact map_actTup (fstA F) g X a i
    · have h1 : projFin (actTup (AF F) (bc (inclR (AF F)) g) X) =
          actTup (Af F) (bc (inclR (Af F)) g) (projFin X) := by
        funext a i
        exact map_actTup (sndA F) g X a i
      rw [h1]
      funext a i
      exact map_actTup (evalV F v) g (projFin X) a i
  have hlocI := local_map σ hCM J hJ g (Ainf F) hLi n _ _ hWi.1 hWi.2 minf minf' hminf hminf' cinf
    (hci _ hWi.1) (hermOf (Ainf F) σ T hT)
  have hlocV := fun v => local_map σ hCM J hJ g (Fv F v) (hLv v) n _ _ (hWv v).1 (hWv v).2 (m v) (m' v) (hm v)
      (hm' v) (c v) (hcv v _ (hWv v).1) (hermOf (Fv F v) σ T hT)
  have key := GlobalTheory.T.euler_product_measure_transport F E σ hCM d b n M _ (κ • minf' (hermOf (Ainf F) σ T hT))
    (κ • minf (hermOf (Ainf F) σ T hT)) (fun v => cfac E v • m' v (hermOf (Fv F v) σ T hT))
    (fun v => cfac E v • m v (hermOf (Fv F v) σ T hT)) (actTup (AF F) (bc (inclR (AF F)) g))
    (actTup (Ainf F) (bc (inclR (Ainf F)) g)) (fun v => actTup (Fv F v) (bc (inclR (Fv F v)) g))
    (measurable_actTup σ hCM (AF F) _) (measurable_of_loc σ hCM (Ainf F) hLi _)
    (fun v => measurable_of_loc σ hCM (Fv F v) (hLv v) _) hproj
    ((GlobalTheory.CompanionTheory.SW.LatRat.latV_rational F E σ hCM d b n M).2.1 g) cinf c hUP
    (by
      rw [Measure.map_smul, hlocI, smul_comm]
      exact (measurable_of_loc σ hCM (Ainf F) hLi _).aemeasurable)
    (fun v => by
      rw [Measure.map_smul, hlocV v, smul_comm]
      exact (measurable_of_loc σ hCM (Fv F v) (hLv v) _).aemeasurable) hfin
    ((isEulerProd_const_iff b _ κ _ _).1 hEul)
  have hth := theta_map (n := n) σ hCM J hJ g He hmat μ 𝓕 T
  rw [hth] at key
  exact (isEulerProd_const_iff b _ κ _ _).2 key

end PositivityTheory.SiegelWeilFormula.Densx

end
