module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMemKsetActsAsGLModSplitPrime
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

theorem _root_.GlobalTheory.T.exists_mem_Kset_acts_as_GL_mod_splitPrime : ∀ (I : AutInst) (N p : ℕ) (w : HeightOneSpectrum (𝓞 I.E)) (fr : PlFrame I N p w), I.n = N → p.Prime → Ideal.absNorm w.asIdeal = p → ¬ IsConj I w w → ∀ M : GL (Fin N) (ZMod p), ∃ x ∈ I.Kset, (∀ (y : I.Lf) (h : I.fmat x *ᵥ (y : Fin I.n → _) ∈ I.Lf), fr.c ⟨_, h⟩ = (M : Matrix (Fin N) (Fin N) (ZMod p)) *ᵥ fr.c y) ∧ ∀ u : HeightOneSpectrum (𝓞 I.E), u ≠ w → ¬ IsConj I w u → ∀ y ∈ I.Lf, (I.fmat x - 1) *ᵥ y ∈ extId I u.asIdeal • I.Lf := by
  first | exact @GlobalTheory.RowLev.exists_mem_Kset_actsAs_trivial_away | exact GlobalTheory.RowLev.exists_mem_Kset_actsAs_trivial_away | (intros; apply GlobalTheory.RowLev.exists_mem_Kset_actsAs_trivial_away <;> assumption)
