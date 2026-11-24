module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTheta
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueGenericPointIntegralSection
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR


theorem _root_.GlobalTheory.T.section_value_generic_point_integral_section : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (w₀ : W0 U) (x : TFK (R := R) (FractionRing R) ⟶ A.A) (e : FrAt x) (h : 𝟙_ (Over (Sp R)) ⟶ G) (l : FractionRing R) (f : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => h.left) (fun _ => 1))), IntTerm.Ext U x h → (∀ (z : (TF (R := R) (FractionRing R)).left) (JA : ((TF (R := R) (FractionRing R)).left ⟶ A.A.left) → A.L.ι) (JG : ((TF (R := R) (FractionRing R)).left ⟶ G.left) → U.LG.L.ι), Good A.L z JA → Good U.LG.L z JG → (Geo.Tor.gw (Y := (TF (R := R) (FractionRing R)).left) w₀ (x.left ≫ U.gen.inv.left) z (JG (toUnit (TF (R := R) (FractionRing R)) ≫ h).left) (fun _ => JA x.left)).val * (val (Z := (TF (R := R) (FractionRing R)).left) e (𝟙 _) z JA).val = GlobalTheory.UT.cst (FractionRing R) z l * (val f (toUnit (TF (R := R) (FractionRing R))).left z JG).val) → ∀ (k : ℕ) (s : SecA A (FractionRing R) k) (σ' : U.SecGF (FractionRing R) k), GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀ (snd (TFK (R := R) (FractionRing R)) ((Over.pullback (jK R)).obj G)).left k (snd (TFK (R := R) (FractionRing R)) A.A).left (U.genF (FractionRing R)).left s (UnifPre.gFK (G := G) (FractionRing R)) (𝟙 _) σ' → ∀ (n : ℕ) (c : Fin n → FractionRing R) (σ : Fin n → H0 U.LG.L k), GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) (FractionRing R)) (fun _ => (k : ℤ)) σ' (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (UnifPre.gFK (G := G) (FractionRing R)) (fun i => scal (fst (TFK (R := R) (FractionRing R)) ((Over.pullback (jK R)).obj G)).left (c i)) → ∀ xs : Fin n → R, (∀ (i : Fin n) (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι), Good U.LG.L z J → sval (σ i) (r ≫ h.left) z J = Geo.Tor.cst r z (xs i) * (val f r z J ^ k).val) → ∀ v : FractionRing R, ValAt s x e v → v * l ^ k = ∑ i, c i * algebraMap R (FractionRing R) (xs i) := by
  first | exact @GlobalTheory.Poinc.IntEval.value_at_section | exact GlobalTheory.Poinc.IntEval.value_at_section | (intros; apply GlobalTheory.Poinc.IntEval.value_at_section <;> assumption)
