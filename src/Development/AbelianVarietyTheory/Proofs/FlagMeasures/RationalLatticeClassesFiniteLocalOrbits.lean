module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasedFlagPairLatticeContainmentStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteClassesLatticesFixedFramePartBoundedScaleStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteIsometriesFixingBothFramesStabilizingLattiStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalOrbitLatticesInfFrameSpanEqStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitLatticeBetweenFrameAndComplementPartsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TotallyPositiveOrthogonalOfTwoFlagExtendedSpacesStatement
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

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.ClFin

theorem classes_finite : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → {h | h ∈ H0 F F' ∧ Formalism.HermitianLatticesTheory.gmap h Λ₀ = Λ₀}.Finite ∧ ∃ S : Finset (LV D), ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ₀) = lattice₂ D Z.M p Λ) → ∃ Λs ∈ S, ∃ γ ∈ H0 F F', Formalism.HermitianLatticesTheory.gmap γ Λs = Λ := by
  intro D X Y u u' F F' w hw hG Z FP hB hR Λ₀ hΛ₀
  have hpos := GlobalTheory.T.totallyPositive_orthogonal_of_two_flagExtendedSpaces D X Y u u' F F' w hw hG
  refine ⟨GlobalTheory.T.finite_isometriesFixingBothFrames_stabilizing_lattice D F F' hpos Λ₀ hΛ₀, ?_⟩
  obtain ⟨N, hN, hNs⟩ := GlobalTheory.T.orbitLattice_between_frameAndComplementParts D X Y u u' F F' w hw hG Z FP hB hR Λ₀ hΛ₀
  obtain ⟨d, c, hd, hc, hdc⟩ := GlobalTheory.T.based_flag_pair_lattice_containment D X Y u u' F F' w hw hG Z FP hB hR Λ₀ (by first | exact hΛ₀ | exact hΛ₀.toIsLattice)
  obtain ⟨S, hS⟩ := GlobalTheory.T.finite_classes_lattices_fixedFramePart_boundedScale D F F' hpos (Λ₀ ⊓ toO (VS D) (Xplus F ⊔ Xplus F')) N d c hN hd hc
  exact ⟨S, fun Λ hΛ hloc => hS Λ hΛ (GlobalTheory.T.localOrbitLattices_inf_frameSpan_eq D X Y u u' F F' w hw hG Z FP hB hR Λ₀ (by first | exact hΛ₀ | exact hΛ₀.toIsLattice) Λ hΛ hloc)
    (hNs Λ hΛ hloc) (hdc Λ hΛ hloc).1 (hdc Λ hΛ hloc).2⟩

end GlobalTheory.Unfold.ClFin
