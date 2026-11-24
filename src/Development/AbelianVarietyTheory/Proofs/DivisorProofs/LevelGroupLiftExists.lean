module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TameInvariantLevelAction
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
public import Formalism.LocalToGlobal.HermitianColumns.CoordinateLatticeSelfDual
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsometryOfSabMap

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoLevel

theorem isBaseFrame_of_isLatBasis {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (h : IsLatBasis V rfl β) :
    IsBaseFrame V β (GlobalTheory.Member.latC V) 1 := by
  refine ⟨fun x => ?_, Formalism.L2.Herm.coordinate_lattice_self_dual D.sp.cm V, Nat.one_pos, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨z, rfl⟩ := GlobalTheory.LiftLevel.swap_surj x
    refine Iff.trans ?_ (h z)
    rw [(GlobalTheory.Member.latHat_eq_hat_and_gram D V).1]
    exact (GlobalTheory.LevSplit.latHat_iff _ z).symm
  · rw [← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq] at hx
    simpa using hx
  · rw [← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq]
    simpa using hx

theorem not_isConjPl_of_le {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : Level H)
    {w w' : Formalism.L2.DIV.Pl D.host.E} (hw : l.Mb ≤ w.asIdeal) (hw' : l.Mb ≤ w'.asIdeal) : ¬ IsConjPl w w' := by
  intro h
  apply w'.isPrime.ne_top
  rw [eq_top_iff, ← l.coprime]
  refine sup_le hw' (Ideal.map_le_iff_le_comap.2 fun a ha => ?_)
  obtain ⟨c', hc', e⟩ := h a (hw ha)
  have : H.bar a = c' := by
    apply RingOfIntegers.coe_injective
    exact (H.bar_eq a).trans e.symm
  show H.bar a ∈ w'.asIdeal
  rw [this]; exact hc'

theorem finR_rfl {D : D7} (V : HSp D) (κ : GA D V) : finR V rfl κ = finE V κ := by
  apply Units.ext
  ext i j
  rfl

end GlobalTheory.GeoLevel
