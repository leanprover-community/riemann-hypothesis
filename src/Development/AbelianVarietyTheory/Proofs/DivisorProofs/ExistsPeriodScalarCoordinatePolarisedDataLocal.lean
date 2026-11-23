module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitValEqMul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemUnitsK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiMemMaximalIdealTendstoZero

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol

namespace GlobalTheory.Mum.TensPol

theorem exists_tauCoord : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : GlobalTheory.PolDeg.Data R) (a b : Q.X),
    ∃ k, Q.TauCoord a b k := by
  intro R _ _ _ Q a b
  obtain ⟨u, hu⟩ := DVR.exists_gen_of_local (V := R) Q.M.L Q.M.isLB (lamPts (Q.c a) (Q.c b)) negε
  have e : ∀ i, (toUnit (TK R)).left ≫ lamPts (Q.c a) (Q.c b) i =
      lamPts (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) i := by
    intro i
    fin_cases i
    · exact congrArg (fun q : TK R ⟶ Q.B => q.left) (MonObj.comp_mul (toUnit (TK R)) (Q.c a) (Q.c b))
    · rfl
    · rfl
    · exact congrArg (fun q : TK R ⟶ Q.B => q.left) (MonObj.comp_one (toUnit (TK R)))
  obtain ⟨t, ht, hv⟩ := exists_gen Q.M.isLB (φ' := fun i => (toUnit (TK R)).left ≫ lamPts (Q.c a) (Q.c b) i) (ε' := negε)
    (fun U _ h => by simp only [e]) (Q.tau a b) (Q.tau_gen a b)
  obtain ⟨c, hc⟩ := exists_unit_val_eq_mul Q.M.isLB ht
    (DVR.pullGen_isGen Q.M.L _ _ u hu (toUnit (TK R)).left)
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom.toMonoidHom c, u, hu, fun z J hJ => ?_⟩
  have ec : unitOn (Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom.toMonoidHom c) = c :=
    Units.ext (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))) _)
  rw [ec, ← hv _ _ z J hJ]
  refine Units.ext ((hc _ (𝟙 _) z J hJ).trans ?_)
  refine congrArg₂ (· * ·) (gs_unit _ z ⊤ trivial _) (congrArg Units.val ((val_pull hJ u _ (𝟙 _)).trans ?_))
  rw [Category.id_comp]

end GlobalTheory.Mum.TensPol
