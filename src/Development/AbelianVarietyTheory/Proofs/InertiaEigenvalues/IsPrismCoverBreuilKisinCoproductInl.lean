module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCoproductFaithfullyFlatModAdicPoStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCoproductIsPushoutBaseChangeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyBreuilKisinPrismCoproductStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismHomMapIdealEqStatement
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isFrame_map {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {B B' : Obj l ↥(OL K)} {t p : B.A}
    (h : IsFrame bk B t p) (k : Hom B B') : IsFrame bk B' (k.f t) (k.f p) := by
  refine ⟨?_, k.f_str _ p h.2⟩
  rw [← GlobalTheory.T.prism_hom_map_ideal_eq l _ B B' k, h.1, Ideal.map_span, Set.image_singleton]

theorem env_inl_cover : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (t p : B.A),
    IsFrame bk B t p → ∀ En : Env bk B t p, Cover En.inl := by
  intro l _ K bk B t p hF En
  refine ⟨⟨fun m => (GlobalTheory.T.breuilKisinPrismCoproduct_faithfullyFlat_mod_adic_pow l K bk B t p En m).flat, fun B' k => ?_⟩, GlobalTheory.T.breuilKisinPrismCoproduct_faithfullyFlat_mod_adic_pow l K bk B t p En⟩
  obtain ⟨En'⟩ := GlobalTheory.T.nonempty_breuilKisinPrismCoproduct l K bk B' (k.f t) (k.f p) (isFrame_map hF k)
  obtain ⟨k', hk'⟩ := GlobalTheory.T.breuilKisinPrismCoproduct_isPushout_base_change l K bk B B' t p k En En'
  exact ⟨En'.Q, k', En'.inl, hk'⟩

end GlobalTheory.BSP
