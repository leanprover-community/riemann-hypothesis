module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelThetaPointOfThetaConstantsLevelSquare
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_level_thetaPoint_of_thetaConstants_level_square : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (rig : LB.Gen (P.L.pull (eSec P.A))) (g m N : ℕ) (hg : P.g = g) (c : Fin N → K) (ze : Γ(Sp K, ⊤)ˣ), rig.IsGen → Odd m → (m : K) ≠ 0 → IsPrimitiveRoot ze (m ^ 2) → HasTh P.A P.L rig m (𝟙 (Sp K)) c → ∃ (lev : Out.Level P (m ^ 2) ze) (β : (Fin (2 * g) → ZMod (m ^ 2)) → Fin N), ∀ mu : K, mu ≠ 0 → IsThetaPt P m (levelPoint lev hg) (fun a => GlobalTheory.ZH.fn (mu * c (β a))) := by
  first | exact @GlobalTheory.UMin.exists_level_isThetaPt_of_hasTh | exact GlobalTheory.UMin.exists_level_isThetaPt_of_hasTh | (intros; apply GlobalTheory.UMin.exists_level_isThetaPt_of_hasTh <;> assumption)
