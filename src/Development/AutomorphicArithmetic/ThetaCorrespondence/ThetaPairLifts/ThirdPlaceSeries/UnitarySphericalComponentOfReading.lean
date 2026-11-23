module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Laws
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RpowNegLeNormOfComponent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitarySphericalSatakeMultisetMapInvStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitarySphericalSatakeOfUnitarisableHasSatakeStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParametersStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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



section
noncomputable section
namespace GlobalTheory.SplitRead
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL
  GlobalTheory.SplitWeil GlobalTheory.RowTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem unitarySphericalComponent_of_reading_alt : GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (T : WDTie N A)
      (S : Reading T), _root_.GlobalTheory.SplitRead.LawsAlt S → RowUnit S → GlobalTheory.RowSatakeBound.UnitarySphericalComponent N A := by
  intro hBZ R H what₂ N A T S hL hU i σ hσ w hw hu
  have hloc := (S i w hw).locW σ hσ
  have hsph : IsSpherical ((S i w hw).row σ).π := by
    rw [← (hL i w hw).sph _ _, ← hloc, ← T.unr]
    exact hu
  obtain ⟨α, hα⟩ := GlobalTheory.T.sphericalRepGL_exists_satakeParameters hBZ _ _ _ hsph
  have hfrob : A.frobEig (A.locW i σ w) =
      (Finset.univ.val.map fun j => (α j : ℂ)).map (·⁻¹) := by
    rw [T.frobEig w _ hu, hloc, (hL i w hw).sat _ _ α hα, Multiset.map_map]
    simp
  have h1 : GlobalTheory.RowSatakeBound.IsUnitarySatakeAt w R.r (Finset.univ.val.map fun j => (α j : ℂ)) :=
    GlobalTheory.T.isUnitarySphericalSatake_of_unitarisable_hasSatake H.E w R.r _ α hα (hU i w hw σ hσ)
  rw [hfrob]
  refine ⟨?_, ?_⟩
  · simpa [Multiset.map_map, Function.comp_def] using h1
  · have := GlobalTheory.RowSatakeBound.finite_residue w
    exact GlobalTheory.T.isUnitarySphericalSatakeMultiset_map_inv _ _ _ _ h1
end GlobalTheory.SplitRead
end
end
