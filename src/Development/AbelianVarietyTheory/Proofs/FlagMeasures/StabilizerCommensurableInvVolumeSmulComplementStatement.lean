module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerCommensurableInvVolumeSmulComplement
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

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.stabilizer_commensurable_invVolume_smul_complement : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), (∀ Λ : Submodule L.O S.V, IsLat L Λ → S.complementReferenceCompactSubgroup.relIndex (S.H0 ⊓ MulAction.stabilizer S.GLV Λ) ≠ 0 ∧ (S.H0 ⊓ MulAction.stabilizer S.GLV Λ).relIndex S.complementReferenceCompactSubgroup ≠ 0 ∧ ∀ h ∈ S.H0, invVol S.complementReferenceCompactSubgroup (S.H0 ⊓ MulAction.stabilizer S.GLV (h • Λ)) = invVol S.complementReferenceCompactSubgroup (S.H0 ⊓ MulAction.stabilizer S.GLV Λ)) ∧ ∀ d Λ, S.IsTerm d Λ → S.complementReferenceCompactSubgroup.relIndex (S.H0 ⊓ MulAction.stabilizer S.GLV d) ≠ 0 ∧ (S.H0 ⊓ MulAction.stabilizer S.GLV d).relIndex S.complementReferenceCompactSubgroup ≠ 0 := by
  first | exact @GlobalTheory.HL.Frames.stab_commensurable_invVol_smul | exact GlobalTheory.HL.Frames.stab_commensurable_invVol_smul | (intros; apply GlobalTheory.HL.Frames.stab_commensurable_invVol_smul <;> assumption)
