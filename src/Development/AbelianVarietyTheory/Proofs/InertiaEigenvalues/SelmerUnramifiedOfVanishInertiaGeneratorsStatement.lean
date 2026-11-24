module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerUnramifiedOfVanishInertiaGenerators
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.selmer_unramified_of_vanish_inertia_generators : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N) (p : PlE D.host) (d : GE N →* Multiplicative (ZMod (X.l i ^ M))) (σ γ : GE N), nu X i + 2 ≤ M → Small2 i s M L z → NewPl i M L p d σ γ → ∀ (A : Type) [CommRing A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ), Kills i A → AntiHom X.cc κ → (∀ g ∈ DecV N p, κ g = 1) → ∀ (Q Q' : Finset (PlE D.host)), (∀ v, v ∈ Q' ↔ v ∈ Q ∨ Over p v) → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (f : GE N → Fin D.R.r → Y), SelC bkP i s κ Y Q' f → (∀ b, f (two X γ b) = 0) → SelC bkP i s κ Y Q f := by
  first | exact @GlobalTheory.NewPrimeUnr.selC_of_vanish | exact GlobalTheory.NewPrimeUnr.selC_of_vanish | (intros; apply GlobalTheory.NewPrimeUnr.selC_of_vanish <;> assumption)
