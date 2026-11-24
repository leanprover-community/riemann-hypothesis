module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientSegmentProductEquivStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleOfContragredientSocle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLengthStatement
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.ExistsSocleSegmentProductStatement
import GroundTheory.LocalFields.PadicLogSeries
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.LkSegExists

theorem hasFiniteLength_prodIrr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL (k := k))
    (hd : ∑ a, (x a).1 = N) : HasFiniteLength (prodIrr x hd) := by
  exact GlobalTheory.T.parabolic_induction_finite_length k (Fin h) (Fin N) (fun a => Fin (x a).1) (stdBlocks (fun a => (x a).1) hd) _
    (piTensor fun a => (x a).rep)
    (isSmooth_piTensor fun a => (x a).snd.rep.smooth)
    (hasFiniteLength_of_isIrreducible (GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA x))

theorem exists_isLSeg : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k), ∃ π : IrrRep (GL (Fin Δ.deg) k), IsLSeg Δ π.ρ := by
  intro k _ _ _ _ hA Δ
  have hd : ∑ a, (Δ.term a).1 = Δ.deg := Δ.sum_term_fst
  obtain ⟨hd', ⟨φ⟩⟩ := GlobalTheory.T.contragredient_segment_product_equiv hA Δ hd
  obtain ⟨τ', hτ'⟩ := GlobalTheory.TL.exists_socle_segment_product hA (segDual Δ) hd'
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompanionTheory.CosocleContra.isCosocle_of_isSocle_contra hA (prodIrr Δ.term hd)
    (isSmooth_prodIrr _ _) (hasFiniteLength_prodIrr hA _ _) τ' (hτ'.of_equiv (.refl _) φ.symm)
  exact ⟨τ, hd, hτ⟩

end GlobalTheory.CompanionTheory.LkSegExists

end
