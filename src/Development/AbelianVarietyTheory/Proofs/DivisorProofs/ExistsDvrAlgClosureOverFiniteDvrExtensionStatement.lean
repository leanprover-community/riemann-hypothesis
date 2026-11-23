module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrAlgClosureOverFiniteDvrExtension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open IsLocalRing

theorem _root_.GlobalTheory.T.exists_dvr_algClosure_over_finite_dvr_extension : ∀ (V W : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr V → GlobalTheory.LN.CDvr W → ∀ io : V →+* W, io.Finite → Function.Injective io → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] [Algebra (FractionRing W) F], (∀ v, algebraMap (FractionRing W) F (algebraMap W _ (io v)) = algebraMap (FractionRing V) F (algebraMap V _ v)) → ∃ N : ℕ, ∀ (T' : Subring F) (_ : IsDiscreteValuationRing T') (f : V →+* T'), (∀ v, (f v : F) = algebraMap (FractionRing V) F (algebraMap V _ v)) → (∀ π, Irreducible π → Irreducible (f π)) → ∃ (T'' : Subring F) (_ : IsDiscreteValuationRing T'') (g : W →+* T'') (e : ℕ), T' ≤ T'' ∧ (∀ w, (g w : F) = algebraMap (FractionRing W) F (algebraMap W _ w)) ∧ 1 ≤ e ∧ e ≤ N ∧ ∀ π, Irreducible π → ∃ ϖ : T'', Irreducible ϖ ∧ Associated (g π) (ϖ ^ e) := by
  first | exact @GlobalTheory.exists_dvr_over_finite_ext | exact GlobalTheory.exists_dvr_over_finite_ext | (intros; apply GlobalTheory.exists_dvr_over_finite_ext <;> assumption)
