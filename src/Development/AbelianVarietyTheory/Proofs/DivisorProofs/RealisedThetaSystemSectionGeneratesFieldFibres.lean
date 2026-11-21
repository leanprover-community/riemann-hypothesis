import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.SiegelTor GlobalTheory.UT
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ThetaLevel

def TorsVals {S : Scheme.{0}} (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))) (T : Over S)
    (θ : LB.Sec (LPow P.A P.L 1 T)) (m : ℕ) {I : Type} (t : I → Γ(T.left, ⊤)) : Prop :=
  ∃ (pt : I → (T ⟶ P.A))
    (fr : ∀ a, LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (pt a).left) (fun _ => 1))),
    (∀ a, IsTorsFrame P rig m (pt a) (fr a)) ∧ (∀ a, IsValueAt P.A P.L 1 θ (pt a) (fr a) (t a)) ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ T.left) (z : Over.mk (x ≫ T.hom) ⟶ P.A), z ^ m = 1 →
      ∃ a, z.left = x ≫ (pt a).left


theorem isGenSec_real {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) :
    IsGenSec ρ.P.A ρ.P.L 1 ρ.th₁ := by
  intro s
  obtain ⟨r, hr, -⟩ := ρ.th₁_basis s
  exact ⟨r 0, fun j => (hr j).trans (Fin.sum_univ_one _)⟩

end GlobalTheory.ThetaLevel
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UMin

theorem isGenSec_real_pull : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] (i : S.R →+* K), IsGenSec ρ.P.A ρ.P.L _ (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) := by
  intro o Ω _ _ _ _ S ρ K _ i
  haveI : IsAffine (Over.mk (𝟙 (Sp S.R))).left := inferInstanceAs (IsAffine (Sp S.R))
  haveI : IsAffine (Over.mk (spMap i ≫ 𝟙 (Sp S.R))).left := inferInstanceAs (IsAffine (Sp K))
  exact GlobalTheory.EmbPull.isGenSec_pullS ρ.P GlobalTheory.abelianSchemeLaws_all.2.secBaseChangeAny _ (GlobalTheory.ThetaLevel.isGenSec_real ρ)

end GlobalTheory.UMin
end
end
