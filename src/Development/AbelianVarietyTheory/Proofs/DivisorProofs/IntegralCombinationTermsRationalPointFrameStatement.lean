module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCombinationTermsRationalPointFrame
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR


theorem _root_.GlobalTheory.T.integral_combination_terms_rational_point_frame : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (g : GtPt D (𝟙_ (Over (Sp R)))) (g' : GtPtF D (FractionRing R)), GtPt.IsPullF (FractionRing R) (toUnit (TF (R := R) (FractionRing R))).left g g' → ∀ (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, g.b.left] (DegPre.lineε 1))) (l : FractionRing R), l ≠ 0 → ∀ (k : ℕ) (wk : Frm D (FractionRing R) k g'.b), wk.IsGen → (∀ (z : (TF (R := R) (FractionRing R)).left) (J : ((TF (R := R) (FractionRing R)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → GlobalTheory.UT.cst (FractionRing R) z (l ^ k) * (val wk (𝟙 _) z J).val = (val t (toUnit (TF (R := R) (FractionRing R))).left z J ^ k).val) → ∀ (s : Fam D (FractionRing R) k) (n : ℕ) (c : Fin n → FractionRing R) (fs : Fin n → ∀ α : D.X, D.SecB k α), (∀ α : D.X, GeneratorPullback.SecLin D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε k) (s.s α) (D.famφB α) (DegPre.famε k) (fun i => fs i α) (DegPre.prB D (FractionRing R)).left (fun i => scal (fst (TF (R := R) (FractionRing R)) D.P.A).left (c i))) → ∀ a : Fin n → D.X → R, (∀ (i : Fin n) (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → sval (fs i α) (r ≫ g.b.left) z J * (val (g.s α) r z J).val * (val t r z J ^ k).val = Geo.Tor.cst r z (a i α) * (val (L := D.P.L) D.rig r z J ^ k).val) → ∀ α : D.X, l ^ k * coef s g' wk α = ∑ i, c i * algebraMap R (FractionRing R) (a i α) := by
  first | exact @GlobalTheory.Poinc.IntEval.coef_comb_pull | exact GlobalTheory.Poinc.IntEval.coef_comb_pull | (intros; apply GlobalTheory.Poinc.IntEval.coef_comb_pull <;> assumption)
