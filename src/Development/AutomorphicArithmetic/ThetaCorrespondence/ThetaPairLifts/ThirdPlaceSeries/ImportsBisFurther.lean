module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalIrreducibleFixedVectorsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockTypeAtSplitPlace
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerTerStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypeVecBlockCharFixedPlaceStatement
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TypeBlockPf
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ i w hw, (∃ k, w ∈ placesOver D.host.E (D.host.g k)) → GlobalTheory.SplitWeil.IsTame (S i w hw).mu → TypeBlock S i w hw := by
  intro hL D P S hT i w hw ⟨k, hk⟩ htame
  refine ⟨htame, fun Q => ?_⟩
  obtain ⟨s, rfl⟩ := splitAt D w hw
  obtain ⟨c, T, hc, hcs, -, -, -⟩ := hT.rep i s hw Q
  have hf : ∃ f ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), f ≠ 0 ∧
      ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x →
        Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t →
        NG.rt D.host.E D.R.nV x f =
          blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • f := by
    obtain ⟨v, e | e⟩ := GlobalTheory.DimPartsCompare.cover k s.w hk
    · exact _root_.GlobalTheory.T.split_place_completion_iso_tame_alt hL D P S hT i k v s hw e htame c hc hcs Q
    · exact _root_.GlobalTheory.T.conjugate_place_completion_iso_tame_alt hL D P S hT i k v s hw e htame c hc hcs Q
  obtain ⟨f, hfS, hf0, hfe⟩ := hf
  obtain ⟨y, hy0, hy⟩ := GlobalTheory.T.local_irreducible_fixed_vectors D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s _
    (hT.rep i s hw Q) c hc hcs (blockGrp _ D.R.r D.R.t) (blockChar (S i s.w hw).mu) (fun h hh => hh.1)
    (fun h hh => ⟨kOne_le_blockGrp _ _ hh, blockChar_kOne _ htame hh⟩) f hfS hf0 hfe
  exact ⟨y, hy0, isBlockVec_of _ _ _ hy⟩
end GlobalTheory.TypeBlockPf
end
