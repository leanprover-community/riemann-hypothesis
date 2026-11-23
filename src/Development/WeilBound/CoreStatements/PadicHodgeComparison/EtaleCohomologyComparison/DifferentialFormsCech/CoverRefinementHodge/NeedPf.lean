module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CoverRefinementHodge.CovRefine
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OmegaPullId
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CovOfLocal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmoothCoordinateCover
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctorId
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace CrystallineSemistableComparison.Om.Nt2

theorem cov_of_local' {O : Type} [CommRing O] {X : Scheme.{0}} (Q : X.Opens → Prop) (q : X ⟶ Spec (CommRingCat.of O))
    [IsSeparated q] [QuasiCompact q] (h : ∀ x : X, ∃ (V : X.Opens) (d : ℕ), x ∈ V ∧ Q V ∧ Nonempty (Pb.Coord q V d)) :
    ∃ U : Pb.Cov q, ∀ α, Q (U.U α) :=
  _root_.UpperTheory.Reformulated.B.Qm13.cov_of_local Q q h

theorem cov_refine : CovRefine := by
  intro K _ X q _ _ _ κ V hV
  refine cov_of_local' (fun W => ∃ k, W ≤ V k) q fun x => ?_
  have hx : x ∈ iSup V := by rw [hV]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨W, hW, hxW, hWk⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := V k) (x := x) hk
  have h : RingHom.Locally RingHom.IsStandardSmooth (q.appLE ⊤ W le_top).hom :=
    RingHom.smooth_iff_locally_isStandardSmooth.1 (q.smooth_appLE (isAffineOpen_top _) hW le_top)
  obtain ⟨f, hf, hst⟩ :=
    GlobalTheory.CompanionTheory.CovEx.exists_basicOpen RingHom.IsStandardSmooth RingHom.isStandardSmooth_respectsIso q hW h hxW
  obtain ⟨n, g, hg, he⟩ := hst.exists_etale_mvPolynomial
  exact ⟨_, n, hf, ⟨k, fun y hy => hWk (X.basicOpen_le f hy)⟩, GlobalTheory.CompanionTheory.CovEx.coord_basicOpen q hW f g hg he⟩

theorem pullH_id : PullHId := fun q h a n x => GlobalTheory.CompanionTheory.HodgePull.pullH_id _ _ q a n x

theorem pullC_id : PullCId := fun q h a j x => GlobalTheory.HodgeCoh.hodgePull_id q a j x

end CrystallineSemistableComparison.Om.Nt2
