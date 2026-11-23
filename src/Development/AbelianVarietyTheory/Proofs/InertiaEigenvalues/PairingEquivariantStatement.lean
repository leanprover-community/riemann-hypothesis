module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PairingEquivariant
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.pairing_equivariant_alt : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (Y' : Type) [AddCommGroup Y'] [Module A Y'] [TopologicalSpace Y'] [DiscreteTopology Y'] (β : Y →+ Y' →+ ZMod (X.l i ^ (nu X i + 1))), Bal A β → ContAction (repOn (Tgl i s) κ Y) ∧ ContAction (repOn ρ κ⁻¹ Y') ∧ (∀ g x y, vecPair D.R.r β (repOn (Tgl i s) κ Y g x) (repOn ρ κ⁻¹ Y' g y) = ((cycMod D.host.E N.Om (X.l i) (nu X i + 1) g : (ZMod (X.l i ^ (nu X i + 1)))ˣ) : ZMod (X.l i ^ (nu X i + 1))) * vecPair D.R.r β x y) ∧ ∀ v, v ∉ placesOver D.host.E (X.l i) → v ∉ Spl i → v ∉ Q → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ τ ∈ Ine (F := D.host.E) B, repOn (Tgl i s) κ Y τ = 1 ∧ repOn ρ κ⁻¹ Y' τ = 1 := by
  first | exact @GlobalTheory.NewPrime.PairEquiv.pairing_equivariant | exact GlobalTheory.NewPrime.PairEquiv.pairing_equivariant | (intros; apply GlobalTheory.NewPrime.PairEquiv.pairing_equivariant <;> assumption)
