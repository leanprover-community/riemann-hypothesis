module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointObjectsTransportAlongConjugationOverFractio
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
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

theorem _root_.GlobalTheory.T.pointObjects_transport_along_conjugation_over_fraction_field : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (r r' : (N.X i → (GE N →* GL (Fin R.nV) (N.O i)))) (ρ ρ' : (N.X i → (GE N →* GL (Fin R.r) (N.O i)))) (π : N.X i), (∀ x, (∃ Pm : GL (Fin R.nV) (KK N i), ∀ g, (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) * (rO N i r x g).map (toK N i) = (rO N i r' x g).map (toK N i) * (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i)))) → (∃ Pm : GL (Fin R.r) (KK N i), ∀ g, (Pm : Matrix (Fin R.r) (Fin R.r) (KK N i)) * (rhoO N i ρ π g).map (toK N i) = (rhoO N i ρ' π g).map (toK N i) * (Pm : Matrix (Fin R.r) (Fin R.r) (KK N i))) → ∀ S : IdempotentChoiceData N i, GoodCongruenceObjects N r ρ π S → ∃ S' : IdempotentChoiceData N i, S'.g0 = S.g0 ∧ GoodCongruenceObjects N r' ρ' π S' := by
  first | exact @GlobalTheory.Proof.pointObjects_transport_along_conjugation_over_fraction_field.main | exact GlobalTheory.Proof.pointObjects_transport_along_conjugation_over_fraction_field.main | (intros; apply GlobalTheory.Proof.pointObjects_transport_along_conjugation_over_fraction_field.main <;> assumption)
