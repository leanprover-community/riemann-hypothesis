module

public import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionRealSubfieldRingEquiv
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCharDescent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.PtEquivApply
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.SplitByCompl

theorem eq_of_w_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s s' : SplitPlace L),
    s.w = s'.w → s = s' := by
  intro L _ _ _ s s' h
  have hv : s.v = s'.v := HeightOneSpectrum.ext (by rw [← s'.w_under, ← s.w_under, h])
  obtain ⟨v, si⟩ := s
  obtain ⟨v', si'⟩ := s'
  dsimp only at hv
  subst hv
  obtain ⟨i, hi, -, hix⟩ := GlobalTheory.SplitCompl.exists_ringEquiv L ⟨v, si⟩
  obtain ⟨i', hi', -, hix'⟩ := GlobalTheory.SplitCompl.exists_ringEquiv L ⟨v, si'⟩
  dsimp only at hix hix'
  generalize hw : SplitPlace.w ⟨v, si⟩ = w at i hix hi
  generalize hw' : SplitPlace.w ⟨v, si'⟩ = w' at i' hix' hi'
  have hww : w = w' := hw.symm.trans (h.trans hw')
  subst hww
  have e : (i' : v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L) = i :=
    DFunLike.coe_injective ((HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield L) v).equalizer
      hi' hi (funext fun y => by
        have h1 := hix (algebraMap _ L y)
        have h2 := hix' (algebraMap _ L y)
        rw [AlgHom.commutes] at h1 h2
        exact h2.trans h1.symm))
  have e' : ∀ x, i' x = i x := fun x =>
    congrArg (fun f : v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L => f x) e
  have hs : si = si' := AlgHom.ext fun x => i.injective (by rw [hix, ← e', hix'])
  rw [hs]

end GlobalTheory.SplitByCompl
