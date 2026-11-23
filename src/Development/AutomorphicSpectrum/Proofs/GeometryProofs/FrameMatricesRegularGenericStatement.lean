module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdUpdateDiv
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameMatricesRegularGeneric
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

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem _root_.GlobalTheory.T.frame_matrices_regular_generic : ∀ (Ω : Type) [Field Ω] (S : Type) [Fintype S] (r n : S → ℕ) (R : Subring Ω) (O : Subring (GenField Ω r)) [IsLocalRing O] (T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω) (N : ∀ s, Matrix (Fin (r s)) (Fin (n s)) Ω) (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), (∀ a ∈ R, algebraMap Ω (GenField Ω r) a ∈ O) → (∀ s, (T s).det ≠ 0) → (∀ s j l, M s j l ∈ R) → (∀ s l j, N s l j ∈ R) → (∀ s, N s * M s = 1) → (∀ q, stepMinor (flagB M T q.1) q.2 (J q) ≠ 0) → (∀ (q : Σ s, Fin (r s)) (J' : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) ∈ O) → ∃ t ∈ ratioRing R (flagB M T) J, t ≠ 0 ∧ t ∈ O ∧ t⁻¹ ∈ O ∧ ∃ h : ∀ a ∈ R, algebraMap Ω (GenField Ω r) a ∈ locSub (ratioRing R (flagB M T) J) t, (((algebraMap Ω (GenField Ω r)).comp R.subtype).codRestrict (locSub (ratioRing R (flagB M T) J) t) (fun a => h a a.2)).Smooth := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.big_cell_smooth | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.big_cell_smooth | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.Cell.big_cell_smooth <;> assumption)
