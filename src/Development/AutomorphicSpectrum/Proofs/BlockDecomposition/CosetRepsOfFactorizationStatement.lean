module

public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.GroupTheory.Coset.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetRepsOfFactorization
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
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPermWOne
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.IsStrictDom
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SatakeComb

@[expose] public section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

theorem _root_.GlobalTheory.T.coset_reps_of_factorization : ∀ (G : Type) [Group G] (I : Subgroup G) (t : G) (P : G → Prop), P 1 → Finite (I ⧸ (I ⊓ I.map (MulAut.conj t).toMonoidHom).subgroupOf I) → (∀ i ∈ I, ∃ u ∈ I, P u ∧ ∃ y ∈ I, t⁻¹ * y * t ∈ I ∧ i = u * y) → ∃ R : Finset G, (1 : G) ∈ R ∧ (∀ r ∈ R, r ∈ I ∧ P r) ∧ ∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I := by
  first | exact @GlobalTheory.CompanionTheory.SatPow.RepsGen.reps_of_quotient_with_property | exact GlobalTheory.CompanionTheory.SatPow.RepsGen.reps_of_quotient_with_property | (intros; apply GlobalTheory.CompanionTheory.SatPow.RepsGen.reps_of_quotient_with_property <;> assumption)
