module

public import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormZeroSetExtensionFieldIffCommonConeZero
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.chowForm_zeroSet_extensionField_iff_common_cone_zero : ∀ (F : Type) [Field F] [CharZero F] (D N d : ℕ) (I : Ideal (MvPolynomial (Fin N) F)) (f : MvPolynomial (Fin (D + 1) × Fin N) F), IsChowForm I D d f → (∀ (Ω : Type) [Field Ω] [Algebra F Ω] (s : Fin D → Fin N → Ω) (ξ y : Fin N → Ω), y ≠ 0 → (∀ g ∈ I, aeval y g = 0) → (∀ i, ∑ j, s i j * y j = 0) → ∑ j, ξ j * y j = 0 → aeval (join s ξ) f = 0) ∧ (∀ (Ω : Type) [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] (s : Fin D → Fin N → Ω) (ξ : Fin N → Ω), aeval (join s ξ) f = 0 → ∃ y : Fin N → Ω, y ≠ 0 ∧ (∀ g ∈ I, aeval y g = 0) ∧ (∀ i, ∑ j, s i j * y j = 0) ∧ ∑ j, ξ j * y j = 0) := by
  first | exact @GlobalTheory.ChowZeroExt.zero_set_ext | exact GlobalTheory.ChowZeroExt.zero_set_ext | (intros; apply GlobalTheory.ChowZeroExt.zero_set_ext <;> assumption)
