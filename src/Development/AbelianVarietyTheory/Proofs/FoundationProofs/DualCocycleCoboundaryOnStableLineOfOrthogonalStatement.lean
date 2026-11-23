module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousMatQApply
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualCocycleCoboundaryOnStableLineOfOrthogonal
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

theorem _root_.GlobalTheory.T.dualCocycle_coboundary_on_stableLine_of_orthogonal : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ), 1 ≤ n → ∀ (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hcont : Continuous W) (S : Finset Pl) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ), μ.comp (toGS Ω (S : Set Pl)) = cycMod ℚ Ω l n → ∀ (B : ValuationSubring Ω) (v : Pl), IsPlaceOver B v → (∀ s ∈ Dec (F := ℚ) B, mat W s 1 0 = 0) → ∀ f : Z1 ((twDual μ (rhoS c n W hint S hN)).comp (locHom (S : Set Pl) B)), (∀ a ∈ ordCond c n W hint S hN B, cupH1H1TwistedDual μ (rhoS c n W hint S hN) (locHom (S : Set Pl) B) ((contAction_rhoS c n W hint S hN hcont).comp' (continuous_locHom _ B)) (Submodule.mkQ _ f) a = 0) → ∃ m : TDual (ZMod (l ^ n)) (Mn c n), ∀ (s : Dec (F := ℚ) B) (u : Qn c n), f.1 s (Pi.single 0 u) = twDual μ (rhoS c n W hint S hN) (locHom (S : Set Pl) B s) m (Pi.single 0 u) - m (Pi.single 0 u) := by
  first | exact @GlobalTheory.Ord2.OrdCob.dual_cob_on_line | exact GlobalTheory.Ord2.OrdCob.dual_cob_on_line | (intros; apply GlobalTheory.Ord2.OrdCob.dual_cob_on_line <;> assumption) | exact @GlobalTheory.Ord2.OrdCob.rhoS_single | exact GlobalTheory.Ord2.OrdCob.rhoS_single | (intros; apply GlobalTheory.Ord2.OrdCob.rhoS_single <;> assumption) | exact @GlobalTheory.Ord2.OrdCob.contAction_rhoL | exact GlobalTheory.Ord2.OrdCob.contAction_rhoL | (intros; apply GlobalTheory.Ord2.OrdCob.contAction_rhoL <;> assumption)
