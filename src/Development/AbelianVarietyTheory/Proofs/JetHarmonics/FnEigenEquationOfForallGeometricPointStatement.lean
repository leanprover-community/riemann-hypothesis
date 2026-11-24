module

public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FnEigenEquationOfForallGeometricPoint
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FieldBaseChange (constVal isoVal)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.fn_eigen_equation_of_forall_geometric_point_alt : ∀ (V O F : Type) [CommRing V] [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F], Function.Injective (algebraMap O F) → ∀ (β : V →+* O) (G : Over (Spec (CommRingCat.of V))) [GrpObj G], Flat G.hom → ∀ (Z : Over (Spec (CommRingCat.of O))), IsFinite Z.hom → Flat Z.hom → IsReduced (Pdiv.specO O F ⊗ Z).left → ∀ (jZ : Z.left ⟶ G.left), jZ ≫ G.hom = Z.hom ≫ Spec.map (CommRingCat.ofHom β) → ∀ (U : G.left.Opens) (l : ℕ) (c : Fin l → O) (s : Fin l → Γ(G.left, U)) (k : Γ(Z.left, ⊤)), (∀ (T : Over (Spec (CommRingCat.of V))) (e : T.left ⟶ Spec (CommRingCat.of F)) (c₀ : Pdiv.specO O F ⟶ Z) (r g : T ⟶ G), g.left = (e ≫ c₀.left) ≫ jZ → ∀ z : T.left, r.left z ∈ U → (r * g).left z ∈ U → ∑ i, constVal e z (algebraMap O F (c i)) * gs (r * g).left z U (s i) = gs (e ≫ c₀.left) z ⊤ k * ∑ i, constVal e z (algebraMap O F (c i)) * gs r.left z U (s i)) → ∀ (T : Over (Spec (CommRingCat.of V))) (q : T.left ⟶ Z.left) (r g : T ⟶ G), g.left = q ≫ jZ → ∀ z : T.left, r.left z ∈ U → (r * g).left z ∈ U → ∑ i, constVal (q ≫ Z.hom) z (c i) * gs (r * g).left z U (s i) = gs q z ⊤ k * ∑ i, constVal (q ≫ Z.hom) z (c i) * gs r.left z U (s i) := by
  first | exact @GlobalTheory.fn_eigen_equation_of_forall_geometric_point | exact GlobalTheory.fn_eigen_equation_of_forall_geometric_point | (intros; apply GlobalTheory.fn_eigen_equation_of_forall_geometric_point <;> assumption)
