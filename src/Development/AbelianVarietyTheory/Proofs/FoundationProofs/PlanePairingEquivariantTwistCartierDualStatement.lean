module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DvdOfMemIk
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PlanePairingEquivariantTwistCartierDual
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

theorem _root_.GlobalTheory.T.planePairing_equivariant_twist_cartierDual : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hdet : dt W ^ 2 = 1) (S : Finset Pl) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ), μ.comp (toGS Ω (S : Set Pl)) = cycMod ℚ Ω l n → ∀ (s : G ℚ Ω) (y : Mn c n), GlobalTheory.Ord2.SelPerp.Phi c n (matQ c n (dual1 W) (CupCob.dual_representation_integral c W hdet hint) s *ᵥ y) = twDual μ (rhoS c n W hint S hN) (toGS Ω (S : Set Pl) s) (GlobalTheory.Ord2.SelPerp.Phi c n y) := by
  first | exact @GlobalTheory.Ord2.SelPerp.Phi_equivariant | exact GlobalTheory.Ord2.SelPerp.Phi_equivariant | (intros; apply GlobalTheory.Ord2.SelPerp.Phi_equivariant <;> assumption) | exact @GlobalTheory.Ord2.SelPerp.matQ_det_sq | exact GlobalTheory.Ord2.SelPerp.matQ_det_sq | (intros; apply GlobalTheory.Ord2.SelPerp.matQ_det_sq <;> assumption) | exact @GlobalTheory.Ord2.SelPerp.matQ_dual1_apply | exact GlobalTheory.Ord2.SelPerp.matQ_dual1_apply | (intros; apply GlobalTheory.Ord2.SelPerp.matQ_dual1_apply <;> assumption)
