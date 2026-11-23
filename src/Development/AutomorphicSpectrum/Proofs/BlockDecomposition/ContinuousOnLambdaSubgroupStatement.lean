module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnLambdaSubgroup
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
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

theorem _root_.GlobalTheory.T.continuousOn_lambda_subgroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (e : Matrix (Fin n) (Fin n) E), e * e = e → (∀ s : (Ad E)ˣ, logAbs (s : Ad E) = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E s : ℝ)) → ∀ H : Subgroup (GA E n), (∀ t ∈ H, t.val * rm e = rm e * t.val) → ContinuousOn (lam e) (H : Set (GA E n)) := by
  first | exact @GlobalTheory.CompanionTheory.TorusCh.continuousOn_lam | exact GlobalTheory.CompanionTheory.TorusCh.continuousOn_lam | (intros; apply GlobalTheory.CompanionTheory.TorusCh.continuousOn_lam <;> assumption)
