module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDatumStructureMapInjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyBreuilKisinDatumStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalHomExtBreuilKisinPrismStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemiBCInjectiveOfInjective
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
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem fHom_eq_of_realises : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (T' : Type) [AddCommGroup T'] [Module ℤ_[l] T']
    (ρ' : ↥(GK K) → (T' →ₗ[ℤ_[l]] T')) (M M' : FCrys l ↥(OL K))
    (j' : M'.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T')),
    Realises K M' (ainfObj K) (ainfId K) T' ρ' j' → ∀ u u' : FHom M M',
      (∀ x, j' (u.u (ainfObj K) x) = j' (u'.u (ainfObj K) x)) → u = u' := by
  intro l _ K T' _ _ ρ' M M' j' H u u' h
  obtain ⟨bk⟩ := GlobalTheory.T.nonempty_breuilKisinDatum l K
  apply GlobalTheory.T.prismaticFCrystalHom_ext_breuilKisin_prism l K bk M M' u u'
  haveI := M'.fin (ainfObj K)
  haveI := M'.proj (ainfObj K)
  haveI := M'.fin bk.prism
  haveI := M'.proj bk.prism
  have hj : Function.Injective j' :=
    semiBC_injective_of_injective _ _ ((inclW l).comp (ainfId K).toRingHom)
      (GlobalTheory.Prism.inclW_injective.comp (ainfId K).injective) _ _ j' H.bc
  have ht : Function.Injective (M'.tr bk.ι) :=
    semiBC_injective_of_injective _ _ bk.ι.f (GlobalTheory.T.breuilKisinDatum_structureMap_injective l K bk) _ _ (M'.tr bk.ι) (M'.tr_bc bk.ι)
  refine LinearMap.ext fun x => ht (hj ?_)
  rw [← u.u_tr, ← u'.u_tr]
  exact h _

end GlobalTheory.BSP
