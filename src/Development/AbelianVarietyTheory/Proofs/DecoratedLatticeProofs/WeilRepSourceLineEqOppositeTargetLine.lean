module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilConjugationAdjointRuleStandardCharStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepConjSourceLineEqTargetLineStatement
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConjugateAdjointDagger
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.ConjLine

theorem weil_source_line_opposite : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (L L' S : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E), L.rank = L'.rank → τᴴ ⬝ (L.gram ⬝ τ) = (((-1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram → ∀ (χz χ χ' : ((AE D)ˣ →* Circle)) (om : Om L S) (om' : Om S L'), IsWeilDatumO ψ L S χz χ om → IsWeilDatumO ψ S L' χ' χz⁻¹ om' → ∀ f, IsThetaFunO ψ L S f → IsThetaFunO ψ S L' (fun w => f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w))) ∧ ∀ h, om' (h, 1) (fun w => f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w))) = fun w => om (1, h) f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)) := by
  intro D ψ L L' S τ hrk hg χz χ χ' om om' hom hom' f hf
  have hstd : IsStdChar D ψ (-1) := hom.std
  have CA := GlobalTheory.T.weilConjugationAdjointRule_standard_char D ψ hstd S L'
  have h1 := (CA.conj_target χ' χz⁻¹ om' hom').1
  rw [inv_inv] at h1
  have hg' : τᴴ ⬝ (L.gram ⬝ τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • (GlobalTheory.ChiGrid.negSp L').gram := by
    rw [hg, GlobalTheory.ChiGrid.negSp_gram]; simp
  have H := GlobalTheory.T.weilRep_conj_sourceLine_eq_targetLine D ψ L (GlobalTheory.ChiGrid.negSp L') S τ hrk hg' χz χ χ'⁻¹ om (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjTarget om') hom h1 f hf
  refine ⟨?_, ?_⟩
  · have := H.1
    exact (CA.theta_neg _).1.mp this
  · intro h
    have key : ∀ F : WO S L' → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjTarget om' (h, 1) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id F) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (om' (h, 1) F) := by
      intro F
      have e := GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cjEnd_cj (Equiv.refl (WO S L')) (om' (h, (GlobalTheory.ChiGrid.negGA L').symm 1)) F
      simpa [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjTarget] using e
    have H2 := H.2 h
    have K : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjTarget om' (h, 1) (fun w => star (f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)))) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (om' (h, 1) (fun w => f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)))) := key (fun w => f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)))
    rw [K] at H2
    funext w
    have := congrArg star (congrFun H2 w)
    simpa [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj] using this

end GlobalTheory.ConjLine
