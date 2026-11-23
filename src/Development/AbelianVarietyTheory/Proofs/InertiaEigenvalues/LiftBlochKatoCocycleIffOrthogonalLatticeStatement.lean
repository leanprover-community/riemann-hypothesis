module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFCocIff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftBlochKatoCocycleIffOrthogonalLattice
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual

theorem _root_.GlobalTheory.T.lift_blochKatoCocycle_iff_orthogonal_lattice : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → ∀ ρ, IsDual i s ρ → ∀ (v : PlE D.host) (hv : v ∈ placesOver D.host.E (X.l i)) (ϖ : X.O0 i), Irreducible ϖ → ∀ y : ↥(DecV N v) → Fin D.R.r → X.O0 i, (∀ a, IsLocallyConstant fun g => IsLocalRing.residue (X.O0 i) (y g a)) → (∀ g h a, y (g * h) a - (y g a + (Tdual i s g.1).mulVec (y h) a) ∈ IsLocalRing.maximalIdeal (X.O0 i)) → ((∃ y', IsFCoc bkP i v hv ρ y' ∧ ∀ g a, y' g a - y g a ∈ IsLocalRing.maximalIdeal (X.O0 i)) ↔ ∀ d, IsFCoc bkP i v hv (Tgl i s) d → ∃ f : ↥(DecV N v) → Formalism.BasicNotions.KmodO (X.O0 i), IsLocallyConstant f ∧ ∀ g h, (Submodule.Quotient.mk ((algebraMap (X.O0 i) (FractionRing (X.O0 i)) ϖ)⁻¹ * algebraMap (X.O0 i) (FractionRing (X.O0 i)) (d g ⬝ᵥ (Tdual i s g.1).mulVec (y h))) : Formalism.BasicNotions.KmodO (X.O0 i)) = ((eps0 X i g.1 : (X.O0 i)ˣ) : X.O0 i) • f h - f (g * h) + f g) := by
  first | exact @GlobalTheory.BKLatticeCochain.lift_iff_orthogonal | exact GlobalTheory.BKLatticeCochain.lift_iff_orthogonal | (intros; apply GlobalTheory.BKLatticeCochain.lift_iff_orthogonal <;> assumption)
