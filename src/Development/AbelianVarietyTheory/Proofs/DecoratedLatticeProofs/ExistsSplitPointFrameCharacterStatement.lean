module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPointFrameCharacter
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel NumberField

theorem _root_.GlobalTheory.T.exists_splitPoint_frame_character : ∀ (D : D7), (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [IsTopologicalRing k] [CharZero k] (T : ℕ), T.Prime → Nat.card (IsLocalRing.ResidueField 𝒪[k]) = T → Irreducible (T : 𝒪[k]) → ∀ (w : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e w → IsSplitIdem D e → Ideal.absNorm w.asIdeal = T → ¬ (w.asIdeal ^ 2 ∣ Ideal.span {(T : 𝓞 D.host.E)}) → ∃ p : SplitPt D k, p.e = e) ∧ ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k), (∀ (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (b : Matrix (Fin S.rank) n k) (b' : Matrix n (Fin S.rank) k), b * b' = 1 → b' * b = 1 → ∃ β : Frame p S n, β.b = b) ∧ ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∃ χ : AddChar k Circle, p.IsChar ψ χ ∧ Continuous χ ∧ χ ≠ 1 ∧ (p.UnitAA → GlobalTheory.SplitWeil.HasConductor χ 1) := by
  first | exact @GlobalTheory.InhPt.exists_splitPt_frame_char | exact GlobalTheory.InhPt.exists_splitPt_frame_char | (intros; apply GlobalTheory.InhPt.exists_splitPt_frame_char <;> assumption)
