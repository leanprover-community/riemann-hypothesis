module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BasisBOfBcOn
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapOAffine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFgPullSqC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedSplittingOverField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftPOfBounds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PdPBotPos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarMultiplicationShiftsFiltration
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensTransportSymm
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

theorem split_field : ∀ {K B : Type} [Field K] [CommRing B] [Algebra K B] {I : Ideal B} (γ : DividedPowers I) (m : ℕ),
    pdP γ m = ⊥ → Nonempty (GrSplit K γ m) := @GlobalTheory.CompanionTheory.GrSplitField.nonempty_grSplit

theorem leC_shift : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) (𝒱 : Set X.Opens) (i : ℕ) (a : A), a ∈ pdP γ i → ∀ r : ℤ,
    (smO γ q l s 𝒱).LeC a (sFil _ (r - i)) (sFil _ r) := @GlobalTheory.CompanionTheory.LecShift.leC_shift

theorem bc_loc : KH.LocBc → KH.PolyTf → BcOn True := @GlobalTheory.CompanionTheory.BcLoc.bc_single

theorem bc_glob : KH.GlobBcSt → BcOn True → BcOn False := @GlobalTheory.CompanionTheory.GlobBc.main

theorem fin_o : KH.LocGr → KH.PolyTf → KH.GlobSerreSt → KH.GrCechFin → FinO := @GlobalTheory.CompanionTheory.FinOverO.finO

theorem afg_a : BcOn False → FinO → AfgA := @GlobalTheory.CompanionTheory.LatticeFinite.afgA_of_bcOn_finO

theorem lift_a : AfgA → LiftA := @GlobalTheory.CompanionTheory.LiftLat.liftA_of_afgA

theorem basis_b : BcOn False → KH.KIso → BasisB := @GlobalTheory.CompanionTheory.BasisBase.basisB_of_bcOn

end CrystallineSemistableComparison.Pb
