module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Formalism.SatakeDualWeyl.StatementG
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.PlaceA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem not_isSplitPl_of_isInertAt (D : D7) (Pp : HeightOneSpectrum (𝓞 D.host.E)) (h : Formalism.UG.IsInertAt (↥D.host.F) D.host.E (HeightOneSpectrum.under (𝓞 ↥D.host.F) Pp) Pp) : ¬ Formalism.BasicNotions.IsSplitPl D.host Pp := by
  rintro ⟨x, hx, hy⟩
  have hc : (NumberField.RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)).comp
      (algebraMap (𝓞 ↥D.host.F) (𝓞 D.host.E)) = algebraMap (𝓞 ↥D.host.F) (𝓞 D.host.E) := by
    refine RingHom.ext fun a => RingOfIntegers.ext ?_
    have key : ((algebraMap (𝓞 ↥D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) = ((a : ↥D.host.F) : D.host.E) := rfl
    have h0 := (D.host.conjE_mem_hostF_iff _).1 (a : ↥D.host.F).2
    show (D.host.conj ((algebraMap (𝓞 ↥D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E)) = _
    rw [key]; exact h0
  have hmem : NumberField.RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E) x ∈ Pp.asIdeal := by
    unfold Formalism.UG.IsInertAt at h
    rw [← h] at hx ⊢
    have := Ideal.mem_map_of_mem (NumberField.RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)) hx
    rwa [Ideal.map_map, hc] at this
  exact hy _ rfl hmem

end GlobalTheory
