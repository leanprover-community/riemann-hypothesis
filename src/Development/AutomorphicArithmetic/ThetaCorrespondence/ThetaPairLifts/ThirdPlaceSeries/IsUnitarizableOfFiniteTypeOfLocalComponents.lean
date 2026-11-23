module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtRows
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalIntegrality
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableOfIsLocS
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinTypRowsExistsIsLocSAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin
namespace GlobalTheory.RowSplitUnit

theorem isUnitarizable_of_finiteType_of_local_components_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D _ rep _ _ _ => ∀ (j : ℕ) (σ : D.what₂.FT), D.what₂.isot j σ ≠ ⊥ → ∀ s : SplitPlace D.host.E, ∃ τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E)), IsLocS (rep σ).S s τ ∧ GlobalTheory.SmGL.IsUnitarisable τ.ρ := by
  intro hN hL
  unfold _root_.GlobalTheory.LiftRef.ForallRowSideParameters
  refine EvG.imp (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev) fun K _ _ _ _ hHost => ?_
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, ?_⟩
  intro B f T hO _ _ _ _ w _ Z Wt hX z p0 Y hHo _ _ _ _ Rw _ M tup Q _ _ j σ _ s
  obtain ⟨hH, hF, -⟩ := hHost (w.st Z) hO
  obtain ⟨τ, hτ⟩ := GlobalTheory.RowLocalRows2.finTyp_rows_exists_isLocS hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins hHo hH hF σ s
  obtain ⟨Bf, k1, k2, k3, k4⟩ := GlobalTheory.RowSphSmall.exists_form_rowRepR hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins σ
  exact ⟨τ, hτ, GlobalTheory.RowSphSmall.isUnitarisable_of_isLocS _ Bf k1 k2 k3 k4 s τ hτ⟩
end GlobalTheory.RowSplitUnit
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin

theorem _root_.GlobalTheory.T.exists_unitarisable_local_component_at_split : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D _ rep _ _ _ => ∀ (j : ℕ) (σ : D.what₂.FT), D.what₂.isot j σ ≠ ⊥ → ∀ s : SplitPlace D.host.E, ∃ τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E)), IsLocS (rep σ).S s τ ∧ GlobalTheory.SmGL.IsUnitarisable τ.ρ := by
  first | exact @_root_.GlobalTheory.RowSplitUnit.isUnitarizable_of_finiteType_of_local_components_alt | exact _root_.GlobalTheory.RowSplitUnit.isUnitarizable_of_finiteType_of_local_components_alt | (intros; apply _root_.GlobalTheory.RowSplitUnit.isUnitarizable_of_finiteType_of_local_components_alt <;> assumption)
end
end
