module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LiftValuationIntegralNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem _root_.GlobalTheory.T.lift_valuation_integral_norm : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing O') C] (A : Lift a C) (u : Cˣ) (r : ℕ → Cˣ) (o : Full D C) (M : Mdl o) (f : O' →+* M.W) (u₀ : M.W), A.ν.IntN → Roots u r → ‖(u : C)‖ < 1 → (u : C) = algebraMap (FractionRing M.W) C (algebraMap _ _ u₀) → (∀ x, algebraMap (FractionRing M.W) C (algebraMap _ _ (f x)) = algebraMap (FractionRing O') C (algebraMap _ _ x)) → ∀ n : ℕ, n.Prime → Odd n → ‖(n : C)‖ = 1 → (∀ j, o.I.ζ (n ^ j) = A.I.ζ (n ^ j) ∧ ∀ p : D.La → (A.N.twist A.be u).QT ((n ^ j) ^ 2), (∀ x, TwRel A.be u (r ((n ^ j) ^ 2)) (A.q _ x) (p x)) → o.Theta (n ^ j) fun x => (A.N.twist A.be u).tx (n ^ j) (p x)) → ∃ (N' : NumD C) (ν' : NumOf M.P.D.toPre C N') (J : NumD.Iso (A.N.twist A.be u) N'), (∀ (x : 𝓞 E) y, ν'.eX (J.e (A.arc.act x y)) = x • ν'.eX (J.e y)) ∧ (∀ j x (p : (A.N.twist A.be u).QT (n ^ j)) (q' : N'.QT (n ^ j)) p' z, TwRel A.be u (r (n ^ j)) (A.q _ x) p → q'.1.1.toAdd = J.e p.1.1.toAdd → J.Rel p.1.2 q'.1.2 → ν'.QPt p' q' → z.left = (o.I.ev (n ^ j) x).left ≫ M.φ → M.P.ToA C (n ^ j) p' z) ∧ ∃ (DW : DegPre M.W) (_ : Module (𝓞 E) DW.X) (oW : letI := H.starRing; DW.OAct (𝓞 E)) (φ : _) (he : _) (w : _) (e : _) (νW : NumOf DW C (A.N.twist A.be u)), GlobalTheory.LN.Match a f u₀ DW oW φ he w e ∧ (∀ y, νW.eX y = e (A.ν.eX y)) ∧ (∀ x, (νW.eA x).left ≫ φ = (A.ν.eA x).left) ∧ GeoIso νW ν' J.toIso := by
  first | exact @GlobalTheory.ModelData.data_of_model | exact GlobalTheory.ModelData.data_of_model | (intros; apply GlobalTheory.ModelData.data_of_model <;> assumption)
