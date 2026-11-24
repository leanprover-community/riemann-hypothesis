module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniversalSelmerCocycleBaseChange
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.exists_universalSelmerCocycle_baseChange : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (M : ℕ) (ι : Type) (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (Q : Finset (PlE D.host)) (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)), Computes bkP i s M d Q Φ → ∀ (B : Type) [CommRing B] [Algebra (X.O0 i) B] (φ : abelian₂ X i M ι →ₐ[X.O0 i] B) (κ : GE N →* Bˣ), (∀ g, ((κ g : Bˣ) : B) = φ (delInv i M d g : (abelian₂ X i M ι)ˣ)) → Kills i B → ∃ Z, Univ bkP i s κ Q (Φ.map φ) Z := by
  first | exact @GlobalTheory.NewPrime.UnivCocycle.main | exact GlobalTheory.NewPrime.UnivCocycle.main | (intros; apply GlobalTheory.NewPrime.UnivCocycle.main <;> assumption)
