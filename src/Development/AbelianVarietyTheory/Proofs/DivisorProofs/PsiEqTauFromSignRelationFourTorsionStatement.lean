module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescalePsiW0
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiEqTauFromSignRelationFourTorsion
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.psi_eq_tau_from_sign_relation_four_torsion : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (O : Type) [CommRing O] [StarRing O] [Module O D.X] (o : D.OAct O) (w : O), w + star w = 1 → ∀ u : GlobalTheory.PsiRescale.FourGen D.P.L (o.onB.act w), Normd u → ∀ gam : LB.Gen (LB.LinComb D.P.L (K := Fin 4) ![(𝟙 D.P.A ^ 5).left, (𝟙 D.P.A ^ 4).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left] ![2, -3, -2, 3]), Normd gam → ∀ p q r : QkPt D F 4, q.y = w • p.y → r.y = (1 + w) • p.y → GtAct o w p.g q.g → GtAct o (1 + w) p.g r.g → ∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → ∀ s s' s'' : ((TF (R := R) F).left.presheaf.stalk z)ˣ, s * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (p.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) = val (p.g.s p.y) (𝟙 _) z J ^ 2 * val gam p.g.b.left z J → s' * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (q.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) = val (q.g.s q.y) (𝟙 _) z J ^ 2 * val gam q.g.b.left z J → s'' * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (r.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) = val (r.g.s r.y) (𝟙 _) z J ^ 2 * val gam r.g.b.left z J → s'' = s ^ 2 * s' → @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.tau p.y (w • p.y)) (jFK (R := R) F) z J) * val u (cP D (TF (R := R) F) p.y).left z J = @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (p.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J := by
  first | exact @GlobalTheory.PsiSignRel.sign_rel | exact GlobalTheory.PsiSignRel.sign_rel | (intros; apply GlobalTheory.PsiSignRel.sign_rel <;> assumption)
