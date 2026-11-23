module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FamilyUniformisationPointsEqMarkedIsometry
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
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.familyUniformisation_points_eq_marked_isometry : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {σ' : KA l →+* ℂ} {g g' : ℕ}
    {ty : Fin g → (E →+* ℂ)} {ty' : Fin g' → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (F' : FamilyUnif Xo σ' ty')
    (hpq : 1 ≤ Dw.p + Dw.q) (hσ : σ' (baseKA l).ρ = H.rt0) (hty : IsTypeFn H Dw.p Dw.q ty)
    (hty' : IsTypeFn H Dw.p Dw.q ty') (π : Fin g ≃ Fin g') (hπ : ∀ j, ty' (π j) = ty j)
    (k : Fin F.n) (k' : Fin F'.n) (P : (F.Di k).La →+ (Fin g → ℂ)) (P' : (F'.Di k').La →+ (Fin g' → ℂ))
    (hP : IsPeriod (F.Di k) ty P) (hP' : IsPeriod (F'.Di k') ty' P') (h : F.u k P = F'.u k' P'), ∃ gam : (F.Di k).La ≃ₗ[𝓞 E] (F'.Di k').La, (∀ a b, (F'.Di k').EF (gam a) (gam b) = (F.Di k).EF a b) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), ∃ x, gam (F.t k a) = F'.t k' a + l.M • x := by
  first | exact @GlobalTheory.PermUnif.isometry_of_point_eq_perm | exact GlobalTheory.PermUnif.isometry_of_point_eq_perm | (intros; apply GlobalTheory.PermUnif.isometry_of_point_eq_perm <;> assumption)
