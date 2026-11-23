module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalInvariantsKilled
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.local_invariants_killed_alt : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M R n : ℕ) (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ : Finset (PlE D.host)) (L : Subgroup (GE N)) (z : GE N) (P : Fin R ⊕ Fin n → PlE D.host), 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A₀ L z P → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (t : A) (a : Fin R ⊕ Fin n → A), IsQ P Q → Setup bkP i s κ Q → Kills i A → IsDual i s ρ → IsChar i κ (fun q => a q * t) (fun q => d (P q)) → (∀ q, IsUnit (a (.inr q))) → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y], ∀ v, v ∈ Spl i ∨ v ∈ Q → ∀ m, (∀ g ∈ DecV N v, repOn ρ κ⁻¹ Y g m = m) → t • m = 0 := by
  first | exact @GlobalTheory.NewPrime.LocInv.local_invariants_killed | exact GlobalTheory.NewPrime.LocInv.local_invariants_killed | (intros; apply GlobalTheory.NewPrime.LocInv.local_invariants_killed <;> assumption)
