module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGlAdaptedBasisMonotoneSubspaceChainStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIsotropicFlagParabolicIffSplitPlaceChainStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIsotropicFlagUnipotentIffSplitChainTrivialStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslatedStandardChainStabilizerRadicalStatement
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing
open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.SplitFlag.isParabRad_parAt : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F))
    (s : SplitAt D.sp.cm.sig V.gram (frameLat V) v) (𝔉 : IsoFlag V), GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.IsParabRad (parAt 𝔉 s)
      ((NLoc 𝔉 v).map (s.equiv : GLoc D.sp.cm.sig V.gram v →* GL (Fin V.rank) (Fv D.host.F v))) := by
  intro D V v s 𝔉
  obtain ⟨d, hd, g₀, hg₀⟩ := GlobalTheory.T.exists_gl_adaptedBasis_monotoneSubspaceChain (GlobalTheory.SplitFlag.flagChain 𝔉 s.emb) (GlobalTheory.SplitFlag.flagChain_mono _ _)
    (GlobalTheory.SplitFlag.flagChain_zero _ _) (GlobalTheory.SplitFlag.flagChain_last _ _ s.cm)
  obtain ⟨hP, hN⟩ := GlobalTheory.T.translated_standard_chain_stabilizer_radical _ d hd g₀ hg₀
  have key : ∀ x : GL (Fin V.rank) (Fv D.host.F v),
      splitHom D.sp.cm.sig V.gram s.emb (s.equiv.symm x) = s.basis * x * s.basis⁻¹ := fun x =>
    splitHom_splitEquivIn_symm s.cm s.herm s.emb s.basis x
  have hmap : ∀ (H : Subgroup (GLoc D.sp.cm.sig V.gram v)) (x : GL (Fin V.rank) (Fv D.host.F v)),
      x ∈ H.map (s.equiv : GLoc D.sp.cm.sig V.gram v →* GL (Fin V.rank) (Fv D.host.F v)) ↔ s.equiv.symm x ∈ H :=
    fun H x => ⟨by rintro ⟨g, hg, rfl⟩; simpa using hg, fun hx => ⟨_, hx, s.equiv.apply_symm_apply x⟩⟩
  have hconj : ∀ (H : Subgroup (GL (Fin V.rank) (Fv D.host.F v))) (x : GL (Fin V.rank) (Fv D.host.F v)),
      x ∈ GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.conjBy (s.basis⁻¹ * g₀) H ↔ s.basis * x * s.basis⁻¹ ∈ GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.conjBy g₀ H := by
    intro H x
    rw [GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.mem_conjBy, GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.mem_conjBy]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  refine ⟨2 * 𝔉.k + 1, d, hd, s.basis⁻¹ * g₀, ?_, ?_⟩
  · ext x
    rw [parAt, hmap, GlobalTheory.T.mem_isotropicFlagParabolic_iff_splitPlaceChain D.sp.cm s.cm s.herm s.emb 𝔉, key, hconj, hP]
  · ext x
    rw [hmap, GlobalTheory.T.mem_isotropic_flag_unipotent_iff_split_chain_trivial D.sp.cm s.cm s.herm s.emb 𝔉, key, hconj, hN]
