module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.AtPlace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace GlobalTheory.PfBCI

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem split_component {π : Submodule ℂ (UA E n → ℂ)} {c : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n)
    (σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E)))
    {w : HeightOneSpectrum (𝓞 E)} (hs : IsSplitAt w) (P : SmIrr (GL (Fin n) (w.adicCompletion E)))
    (hsub : GlobalTheory.SmGL.IsSubquotient P.ρ (locProd h w (σ · w)))
    (hsph : IsUnramU π w → GlobalTheory.LGrp.IsSpherical P.ρ (GlobalTheory.LFun.KGL w (n := n)))
    (hc : IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) P.ρ) : AtPlace π h σ w P := by
  exact ⟨hsub, hsph, fun _ _ _ hconj hinv _ _ => absurd hs (GlobalTheory.BcSpehCompare.not_isSplitAt hconj hinv.2.1), fun _ => hc⟩

end GlobalTheory.PfBCI

end
