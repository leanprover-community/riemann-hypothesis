module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedInvariantPairingCharacter
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet

@[expose] public section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair


theorem _root_.GlobalTheory.T.twisted_invariant_pairing_character : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n s : ℕ) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B₀ : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), (∀ (y : Fin (n + 1) → k) v v', B₀ (T (uM (n + 1) y) v) v' = ((ψ (y (Fin.last n)) : Circle) : ℂ) * B₀ v v') → (∀ (y : Fin (n + 1) → k) v v', B₀ v (T' (uM (n + 1) y) v') = ((ψ (-y (Fin.last n)) : Circle) : ℂ) * B₀ v v') → (∀ (p : Mir k n) v v', B₀ (T (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v) (T' (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v') = ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * B₀ v v') → (∀ v, v ∉ twKer T (MirUin k (n + 1)) (mirChar k ψ n) → ∃ v', B₀ v v' ≠ 0) → ∃ B' : TwJacquet T (MirUin k (n + 1)) (mirChar k ψ n) →ₗ[ℂ] TwJacquet T' (MirUin k (n + 1)) (mirChar k ψ⁻¹ n) →ₗ[ℂ] ℂ, (∀ (p : Mir k n) w w', B' (phiMinus k ψ T p w) (phiMinus k ψ⁻¹ T' p w') = ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * B' w w') ∧ (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0) := by
  exact @GlobalTheory.CompanionTheory.MirPair.Descend.descend
