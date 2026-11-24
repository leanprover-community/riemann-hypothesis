module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenTransl
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateCubicalBundlePrincipalPolarisatio
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_translateCubicalBundle_principalPolarisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∀ a : Over.mk (jK R) ⟶ G, a * a = 1 → ∃ (P₁ : GlobalTheory.UU.CP G) (A₁ : PolAV (Sp (FractionRing R))) (gen₁ : (Over.pullback (jK R)).obj G ≅ A₁.A), IsMonHom gen₁.hom ∧ LBIso (A₁.L.pull gen₁.hom.left) (P₁.L.L.pull (pullback.fst G.hom (jK R))) ∧ LBIso (abelian₂ G P₁.L.L) (abelian₂ G P.L.L) ∧ GlobalTheory.GenTransl.IsGenTransl G P.L.L P₁.L.L a := by
  first | exact @GlobalTheory.Mum.exists_transl_pkg | exact GlobalTheory.Mum.exists_transl_pkg | (intros; apply GlobalTheory.Mum.exists_transl_pkg <;> assumption)
