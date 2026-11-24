module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplementOfCharactersUniqueUpToConj
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

theorem _root_.GlobalTheory.T.complement_of_characters_unique_up_to_conj : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (r r' : (N.X i → (GE N →* GL (Fin R.nV) (N.O i)))) (ρ ρ' : (N.X i → (GE N →* GL (Fin R.r) (N.O i)))) (π : N.X i), IsSSRep (mapRep (algebraMap (N.O i) (Kf N i)) (r π)) → (∃ Pm : GL (Fin R.nV) (KK N i), ∀ g, (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) * (rO N i r π g).map (toK N i) = (rO N i r' π g).map (toK N i) * (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i))) → (∃ e, IsDecomp (t := R.t) (r π) (ρ π) (N.chi i) e) → (∃ e, IsDecomp (t := R.t) (r' π) (ρ' π) (N.chi i) e) → (∃ Pm : GL (Fin R.r) (KK N i), ∀ g, (Pm : Matrix (Fin R.r) (Fin R.r) (KK N i)) * (rhoO N i ρ π g).map (toK N i) = (rhoO N i ρ' π g).map (toK N i) * (Pm : Matrix (Fin R.r) (Fin R.r) (KK N i))) := by
  first | exact @GlobalTheory.CharCancel.main | exact GlobalTheory.CharCancel.main | (intros; apply GlobalTheory.CharCancel.main <;> assumption)
