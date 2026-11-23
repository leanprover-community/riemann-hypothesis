module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsWeilOnOfCoord
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoordSymm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumEqTraceOriented
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
import Mathlib.Tactic.Linter.Style
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.OrientedCoord GlobalTheory.Mem.WeilTransport
open scoped TensorProduct

namespace GlobalTheory.Mem.WeilEqRank

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isCoord_coord (S T : HSp D) (hr : S.rank ≤ T.rank) : IsCoord S T S T (coord S T) := {
  cont := continuous_coord S T
  cont' := continuous_coord_symm S T
  sympl := symplOH_eq S T hr
  rat x := by
    constructor
    · rintro ⟨γ, rfl⟩
      exact ⟨(γ * S.gram⁻¹)ᵀ, (coord_ratW S T γ).symm⟩
    · rintro ⟨γ, hγ⟩
      have hγ' : ratW S T γ = coord S T x := hγ
      refine ⟨γᵀ * S.gram, ?_⟩
      change ratW T S _ = x
      rw [← coord_symm_ratW, hγ', AddEquiv.symm_apply_apply]
  inf x := ⟨coord_map_zero S T _ x, fun h => by
    simpa only [AddEquiv.symm_apply_apply] using coord_symm_map_zero S T _ _ h⟩
  fin x := ⟨coord_map_zero S T _ x, fun h => by
    simpa only [AddEquiv.symm_apply_apply] using coord_symm_map_zero S T _ _ h⟩
  part a x h i j := by
    show a * ∑ k, x j k * incA D (S.gram⁻¹ k i) = ∑ k, x j k * incA D (S.gram⁻¹ k i)
    simp only [Finset.mul_sum, ← mul_assoc, h] }

theorem weilOnEqEx_of_weilRepresentation : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ D : D7, WeilOnEqEx D := by
  intro hP D ψ hψ V W χ χ' ⟨hr, h1, h2, h3, h4⟩
  obtain ⟨om, H⟩ := hP D ψ V W χ χ' hψ h1.1 h2.1 h3 h4
  refine exists_isWeilOn_of_coord (isCoord_coord V W hr.le) H (MonoidHom.id _) continuous_id
    (fun g h x => (GlobalTheory.OrientedSmall.bridgeSmall D V W hr.le).2 g h x) (fun _ a _ b => ⟨a, b⟩)
    fun e g h hg hh x y hx hy => ⟨x, y, hg, hh, hx, hy, ?_⟩
  unfold splitFacO splitFac
  rw [if_pos hr.le]

end GlobalTheory.Mem.WeilEqRank

end
