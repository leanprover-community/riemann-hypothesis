module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericIsoOfUniformisationsIsoData
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

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_generic_iso_of_uniformisations_isoData : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D D' : DegData R I) (A A' : PolAV (Sp (FractionRing R))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre), ∃ ψ : A'.A ≅ A.A, IsMonHom ψ.hom ∧ LBIso A'.L (A.L.pull ψ.hom.left) ∧ (∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (p' : QkPt D'.toPre F k) (x' : TFK (R := R) F ⟶ A'.A), p'.y = hD.xe.symm p.y → IsPullGtF (RingHom.id R) hD F p.g p'.g → (QkToAkU U'.toUnifPre F k p' x' ↔ QkToAkU U.toUnifPre F k p (x' ≫ ψ.hom))) ∧ ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X] (o : D.OAct O) (o' : D'.OAct O) (oA : A.OAct O) (oA' : A'.OAct O) (oG : RingAct G O) (oG' : RingAct G' O), U.OLinear O o oA oG → U'.OLinear O o' oA' oG' → (∀ (x : O) y, hD.xe (x • y) = x • hD.xe y) → (∀ x, o'.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (o.onB.act x)) → ∀ x, oA'.act x ≫ ψ.hom = ψ.hom ≫ oA.act x := by
  first | exact @GlobalTheory.exists_generic_iso_of_unif | exact GlobalTheory.exists_generic_iso_of_unif | (intros; apply GlobalTheory.exists_generic_iso_of_unif <;> assumption)
