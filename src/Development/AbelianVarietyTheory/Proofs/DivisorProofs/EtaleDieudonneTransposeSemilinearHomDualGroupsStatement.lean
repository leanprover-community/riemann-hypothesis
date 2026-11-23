module

public import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleDieudonneTransposeSemilinearHomDualGroups
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

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

theorem _root_.GlobalTheory.T.etaleDieudonneTranspose_semilinearHom_dualGroups : ∀ (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn)) (k k' : Type) [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p] [PerfectRing k' p] [Algebra k k'] (G : PDivGroup p k) (G' : PDivGroup p k') (hd : G.dual.IsConn) (hd' : G'.dual.IsConn) (hb : (G.dual.baseChange k').IsConn) (s : SemiHom (algebraMap k k') G' G) (l : Module.Dual (WittVector p k) (B.M G.dual hd)), ∃! l' : Module.Dual (WittVector p k') (B.M G'.dual hd'), ∃ lb : Module.Dual (WittVector p k') (B.M (G.dual.baseChange k') hb), (∀ x, lb (B.smap hb hd (G.dual.toBase k') x) = WittVector.map (algebraMap k k') (l x)) ∧ ∀ y, l' y = lb (B.map hb hd' ((PerfdLat.dualBaseChange k' G).inv ≫ dualHom G' (G.baseChange k') s.lift) y) := by
  first | exact @GlobalTheory.semiHom_dual_transpose | exact GlobalTheory.semiHom_dual_transpose | (intros; apply GlobalTheory.semiHom_dual_transpose <;> assumption)
