module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomKerEqIffFrobeniusTwist
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TypedPartSplitPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueEqZeroIffV
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Mathlib.RingTheory.MvPowerSeries.Basic
import ReciprocityTheory.DualLattices.TensorSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

theorem _root_.GlobalTheory.T.ringHom_ker_eq_iff_frobeniusTwist : ∀ (R k : Type) [CommRing R] [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (f : R →+* k) (h : ℕ), 0 < h → Nat.card (R ⧸ RingHom.ker f) = p ^ h → (∀ x : k, x ^ p ^ h = x → ∃ a, f a = x) ∧ ∃ F : ZMod h → (R →+* k), (∀ s a, F s a = f a ^ p ^ s.val) ∧ (∀ s a, F (s + 1) a = F s a ^ p) ∧ Function.Injective F ∧ ∀ g : R →+* k, RingHom.ker g = RingHom.ker f ↔ ∃ s, F s = g := by
  first | exact @GlobalTheory.FrobOrbit.ringHom_ker_eq_iff_frobenius_twist | exact GlobalTheory.FrobOrbit.ringHom_ker_eq_iff_frobenius_twist | (intros; apply GlobalTheory.FrobOrbit.ringHom_ker_eq_iff_frobenius_twist <;> assumption)
