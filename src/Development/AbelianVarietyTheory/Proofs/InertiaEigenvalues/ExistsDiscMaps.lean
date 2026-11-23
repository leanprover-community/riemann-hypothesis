module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFlatRadiusIdealFactsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClosedDiscExtensionBreuilKisinHomStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClosedDiscExtensionOfPowDvdStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisActionExtendsToAinfDiscRingsStatement
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_discMaps : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ (A A' : Type) [CommRing A] [CommRing A'] (f : A →+* A') (u : A) (u' : A') (ρ ρ' : ℝ≥0) (k : ℕ), 0 < ρ' → u' ^ k ∣ f u → ρ' ^ k ≤ ρ → ∃ F : Disc l u ρ →+* Disc l u' ρ', IsDiscMap (l := _) (u := _) (ρ := _) f F) ∧ (∀ (ρ : ℝ≥0), 0 < ρ → ∀ g : GQ l, ∃ G : bk.DA ρ →+* bk.DA ρ, IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA g) G) ∧ (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ ≤ 1 → ∃ F : bk.DS ρ →+* Disc l (BK.hf f X) ρ, IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf g) F) ∧ 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 ∧ bk.ρ₀ ^ bk.Ep.natDegree = (l : ℝ≥0)⁻¹ := by
  intro l _ K bk
  exact ⟨GlobalTheory.T.exists_closedDiscExtension_of_pow_dvd l, (GlobalTheory.T.galois_action_extends_to_ainf_disc_rings l K bk).2, GlobalTheory.T.exists_closedDisc_extension_breuilKisinHom l K bk,
    (GlobalTheory.T.breuilKisin_flat_radius_ideal_facts l K bk).2.2.1⟩

end GlobalTheory.BSP
