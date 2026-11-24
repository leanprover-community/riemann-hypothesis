module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulSubEqZeroOfSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentsCoarsenToLowerLevel
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

theorem _root_.GlobalTheory.T.idempotents_coarsen_to_lower_level : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l) (t : PAlg l) (r : ℕ → t.A), (∀ m, r (m + 1) ^ l = r m) →
  ∀ {m n : ℕ} (h : m ≤ n) (e : ZMod (l ^ n) → t.A), CompleteOrthogonalIdempotents e →
  (∀ c, t.sharp (e c) * (t.sharp (r n) - t.sharp (t.s (ε.e n)) ^ c.val) = 0) →
  CompleteOrthogonalIdempotents (fun c : ZMod (l ^ m) => ∑ c' with ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c' = c, e c') ∧
  ∀ c : ZMod (l ^ m), t.sharp (∑ c' with ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c' = c, e c') * (t.sharp (r m) - t.sharp (t.s (ε.e m)) ^ c.val) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.ContUniv.coi_descend | exact GlobalTheory.CompanionTheory.ContUniv.coi_descend | (intros; apply GlobalTheory.CompanionTheory.ContUniv.coi_descend <;> assumption)
