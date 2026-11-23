module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricLevelCharacterEqInvBlockDet
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

theorem _root_.GlobalTheory.T.parahoricLevelCharacter_eq_inv_blockDet : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (PP : HeightOneSpectrum (𝓞 E)) (ι : E →+* k), (∀ z : 𝓞 E, valuation k (ι z) < 1 → z ∈ PP.asIdeal) → (∀ y : k, y ∈ 𝒪[k] → ∃ z : 𝓞 E, valuation k (y - ι z) < 1) → ∀ (K T s j d : ℕ) (hd : j + d = s + 1) (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ) (ξ : (𝓞 E ⧸ PP.asIdeal)ˣ →* ℂˣ), (∀ (z : 𝓞 E) (u : kˣ) (r : (𝓞 E ⧸ PP.asIdeal)ˣ), (u : k) = ι z → (r : 𝓞 E ⧸ PP.asIdeal) = Ideal.Quotient.mk PP.asIdeal z → δ u = (ξ r)⁻¹) → ∀ (n : ℕ) (e : Ix (Fin K ⊕ Fin (s + 1)) (Fin T) j ≃ Fin n), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e → ∀ (x : GL (XIx (Fin K) (Fin T) j ⊕ Fin d) k) (hx : x ∈ ((twistChain s (Fin T) (Fin K) δ hδ η).lev j d hd).J) (R : GL (Fin n) (𝓞 E ⧸ PP.asIdeal)), (∀ (a a' : Fin n) (z : 𝓞 E), R.val a a' = Ideal.Quotient.mk PP.asIdeal z → valuation k (x.val (stdOrd (Fin K) (Fin T) j d hd (e.symm a)) (stdOrd (Fin K) (Fin T) j d hd (e.symm a')) - ι z) < 1) → R ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (K + (s + 1))) → (ξ (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 (K + (s + 1))) 1 R))⁻¹ = ((twistChain s (Fin T) (Fin K) δ hδ η).lev j d hd).lam ⟨x, hx⟩ := by
  first | exact @GlobalTheory.LevChr.lam_eq_inv_xi | exact GlobalTheory.LevChr.lam_eq_inv_xi | (intros; apply GlobalTheory.LevChr.lam_eq_inv_xi <;> assumption)
