module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedTorsionTorusExtensionRespectCubical
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

theorem _root_.GlobalTheory.T.framed_torsion_torus_extension_respect_cubical : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ N : ℕ, 1 ≤ N → ∀ (ρ : LB.Gen (A.L.pull (eSec A.A))) (hρ : ρ.IsGen) (c : CubicalStr A.A ⟨A.L, ρ, A.isLB, hρ⟩) (g : Finset (Fin 3) → GtPtF D.toPre (FractionRing V)) (w : ∀ S, Frm D.toPre (FractionRing V) 1 (g S).b) (x : Finset (Fin 3) → (TFK (R := V) (FractionRing V) ⟶ A.A)) (e : ∀ S, FrAt (x S)), x ∅ = 1 → x {0, 1} = x {0} * x {1} → x {0, 2} = x {0} * x {2} → x {1, 2} = x {1} * x {2} → x {0, 1, 2} = x {0} * x {1} * x {2} → (∀ S, (∃ o, GtPtF.IsNsmul N (g S) o ∧ o.IsZero) ∧ (w S).IsGen ∧ (e S).IsGen ∧ LiesOver U.toUnifPre w₀ (g S) (w S) (x S) (e S)) → ∀ (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JB : ((TF (R := V) (FractionRing V)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good A.L z JA → Good D.toPre.P.L z JB → @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {0, 1, 2}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {0}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {1}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {2}) (𝟙 _) z JA) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {0, 1, 2}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {0}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {1}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {2}) (𝟙 _) z JB)) * cubV D.toPre.cub z JB (g {0}).b (g {1}).b (g {2}).b = @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (cubV c (T := TFK (R := V) (FractionRing V)) z JA (x {0}) (x {1}) (x {2})) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {0, 1}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {0, 2}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {1, 2}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e ∅) (𝟙 _) z JA)) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {0, 1}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {0, 2}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {1, 2}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w ∅) (𝟙 _) z JB)) := by
  first | exact @GlobalTheory.Poinc.Sep.LiesCube.cube_of_liesOver | exact GlobalTheory.Poinc.Sep.LiesCube.cube_of_liesOver | (intros; apply GlobalTheory.Poinc.Sep.LiesCube.cube_of_liesOver <;> assumption)
