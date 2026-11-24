module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCompatibleConjugationRepresentation
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.inertia_compatible_conjugation_representation : ∀ D : D7, FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ (w : PlE D.host) (B : ValuationSubring D.nd.Om), w ∉ placesOver D.host.E (D.nd.l i) → IsPlaceOver (F := D.host.E) B w → ∀ s ∈ Ine (F := D.host.E) B, ∀ s' : G D.host.E D.nd.Om, (∀ y, s' (D.ntw.cc y) = D.ntw.cc (s y)) → ((ρ s' : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly = ((ρ s⁻¹ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly ∧ D.nd.chi i 1 s' = D.nd.chi i 1 s⁻¹ := by
  first | exact @GlobalTheory.ConjPoly.conj_inertia | exact GlobalTheory.ConjPoly.conj_inertia | (intros; apply GlobalTheory.ConjPoly.conj_inertia <;> assumption)
