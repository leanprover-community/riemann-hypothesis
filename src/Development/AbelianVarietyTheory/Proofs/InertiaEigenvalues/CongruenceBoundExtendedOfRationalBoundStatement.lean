module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceBoundExtendedOfRationalBound
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut

theorem _root_.GlobalTheory.T.congruenceBound_extended_of_rationalBound : ∀ (D : D7) (i : D.nd.Loc) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), π ∈ D.nd.Z i → (∀ v ∈ D.nd.Q i, D.nd.zeta i v ≠ 1) → (Br.sFin D.loc D.nbr i (fun _ => ρ) π → (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) → D.nd.vcc i π ≤ Br.sPi D.loc D.nbr i (fun _ => ρ) π + (∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℚ)) + (padicValNat (D.nd.l i) (hE D.host) : ℚ) + (D.R.t : ℚ) * ∑ q ∈ D.nd.Q i, lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i q - 1})) → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.vCC D i π ≤ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sPi D i π ρ + GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.shaSum D i + GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.vClass D i + GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.epsQ D i := by
  first | exact @GlobalTheory.Proof.congruenceBound_extended_of_rationalBound.congBound_of_rational | exact GlobalTheory.Proof.congruenceBound_extended_of_rationalBound.congBound_of_rational | (intros; apply GlobalTheory.Proof.congruenceBound_extended_of_rationalBound.congBound_of_rational <;> assumption)
