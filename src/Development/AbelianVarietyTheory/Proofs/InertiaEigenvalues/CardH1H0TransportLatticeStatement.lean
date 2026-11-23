module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.StatementLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH1H0TransportLattice
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.card_H1_H0_transport_lattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (I : Submodule O ↥LA.T) (hI : StableSub LA I) (N : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod N) M] [TopologicalSpace M] [DiscreteTopology M] (e : (↥LA.T ⧸ I) ≃+ M) (rho : Representation (ZMod N) (Formalism.GaloisCohomology.GK l K.1) M), (∀ g x, rho g (e x) = e (actQ LA I hI ((IntermediateField.fixingSubgroupEquiv K.1).symm g) x)) → Nat.card (QuotientCohomology LA I hI) = Nat.card (ReciprocityTheory.Gal.H1 rho) ∧ Nat.card {x : ↥LA.T ⧸ I // ∀ g, actQ LA I hI g x = x} = Nat.card (ReciprocityTheory.Gal.H0 rho) := by
  first | exact @GlobalTheory.GaloisTransport.card_H1_H0_transport | exact GlobalTheory.GaloisTransport.card_H1_H0_transport | (intros; apply GlobalTheory.GaloisTransport.card_H1_H0_transport <;> assumption)
