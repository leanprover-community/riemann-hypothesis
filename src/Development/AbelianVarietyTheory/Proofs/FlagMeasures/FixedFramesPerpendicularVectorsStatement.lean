module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
public import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFramesPerpendicularVectors
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

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fixed_frames_perpendicular_vectors : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → IsSplit D F0 Λ → ∀ (P : LatW D) (φ : P →ₗ[𝓞 D.host.E] (hS D).V) (Z : GramM D), (∀ p, φ p ∈ XLam Λ (lf D F0)) → P ≤ L0X D Λ (lf D F0) → ∀ F' ∈ FixSet D Λ (lf D F0) ((Tu D u' : ℕ) : D.host.E) Z P φ, ∃ w : Fin (D.R.rS + 1) → (D.sp.X 0).V, (∀ b, IsWcomp D P (frame F' b) (w b) ∧ w b ∈ dualInH (D.sp.X 0).hT (perpW D (L0X D Λ (lf D F0)) P)) ∧ ((Tu D u : ℕ) : D.host.E) * (D.sp.X 0).hT (∑ b, Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec (Z.submatrix Fin.castSucc id) b • w b) (∑ b, Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec (Z.submatrix Fin.castSucc id) b • w b) = Gmat D ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E) Z := by
  first | exact @GlobalTheory.LoopC.WMem.main | exact GlobalTheory.LoopC.WMem.main | (intros; apply GlobalTheory.LoopC.WMem.main <;> assumption)
