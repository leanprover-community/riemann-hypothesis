module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRedDual
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleDieudonneTransposeAbsFrobeniusApplyF
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

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.Dieu.EtFromConn

theorem _root_.GlobalTheory.T.etaleDieudonneTranspose_absFrobenius_apply_F : ∀ (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn)) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : G.IsEt) (l l' : Mod B G h), IsTr B (frobRing (p_eq_zero p k)) h h (absFrob (p_eq_zero p k) G) l l' → ∀ y, l' (B.F G.dual (dual_conn h) y) = p * WittVector.frobenius (l y) := by
  first | exact @GlobalTheory.Dieu.EtFromConn.isTr_absFrob_F | exact GlobalTheory.Dieu.EtFromConn.isTr_absFrob_F | (intros; apply GlobalTheory.Dieu.EtFromConn.isTr_absFrob_F <;> assumption)
