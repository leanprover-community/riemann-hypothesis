module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetQuotientEigenvector
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentationIff

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace PositivityTheory.Pf1.SegRepC.PiLocalization₂

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]



set_option synthInstance.maxHeartbeats 400000 in
theorem isSubquotient_jac_of_le {d l : ℕ} (σ : IrrRep (GL (Fin d) k))
    {S T : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l))} (hST : S.toSubmodule ≤ T.toSubmodule)
    {X : Type} [AddCommGroup X] [Module ℂ X] {π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X}
    (h : IsSubquotient π (jac (consecBlocks l d) S.toRepresentation)) :
    IsSubquotient π (jac (consecBlocks l d) T.toRepresentation) :=
  h.trans (GlobalTheory.JacquetExact.isSubquotient_jac (d := fun _ => d) (consecBlocks l d)
    (GlobalTheory.CompanionTheory.JacExp.isSmooth_sub (isSmooth_parInd _ _) T)
    (IsSubquotient.of_injective ⟨Submodule.inclusion hST, fun _ => rfl⟩ (Submodule.inclusion_injective hST)))

end PositivityTheory.Pf1.SegRepC.PiLocalization₂

end
