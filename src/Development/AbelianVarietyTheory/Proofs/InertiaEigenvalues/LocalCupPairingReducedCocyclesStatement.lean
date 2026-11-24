module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCupPairingReducedCocycles
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

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.Published.PoitouTate GlobalTheory.ResSel

theorem _root_.GlobalTheory.T.local_cup_pairing_reduced_cocycles : LocalTateDuality → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ (K : Type) [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K], IsRes i K → ∀ ρ, IsDual i s ρ → ∀ v ∈ placesOver D.host.E (X.l i), ∀ (x : Z1 ((red i K (Tgl i s)).comp (DecV N v).subtype)) (y : Z1 ((red i K ρ).comp (DecV N v).subtype)), Submodule.Quotient.mk x ∈ bkOn bkP i (Tgl i s) (1 : GE N →* Kˣ) K v → Submodule.Quotient.mk y ∈ bkOn bkP i ρ (1 : GE N →* Kˣ) K v → ∀ (lam : K →+ ZMod (X.l i ^ 1)) (w : Z2 (muLoc D.host.E (X.l i) 1 (N.plOm.1 v))), (∀ g h : ↥(DecV N v), w.1 (g, h) = lam (x.1 g ⬝ᵥ red i K ρ g (y.1 h))) → (Submodule.Quotient.mk w : H2 (muLoc D.host.E (X.l i) 1 (N.plOm.1 v))) = 0 := by
  first | exact @GlobalTheory.CupAbove.cup_eq_zero_above | exact GlobalTheory.CupAbove.cup_eq_zero_above | (intros; apply GlobalTheory.CupAbove.cup_eq_zero_above <;> assumption)
