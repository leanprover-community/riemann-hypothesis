import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfTrivial

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped Pointwise

def QkExtExistsSt : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (D : Out.DegPre R) (F F' : Type) [Field F] [Algebra (FractionRing R) F]
    [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F'),
    (∀ r : FractionRing R, f (algebraMap _ F r) = algebraMap _ F' r) →
    ∀ (k : ℕ) (p : Out.QkPt D F k), ∃ p' : Out.QkPt D F' k, QkExt f p p'

def LevelSpanBSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l)
    (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing k) F]
    (x : Out.TF (R := k) F ⟶ a.D₀.P.A), (letI := H.starRing; ∀ m ∈ l.Mb, x ≫ a.oa.onB.act m = 1) →
    x ∈ Subgroup.closure ({z | ∃ χ, z = toUnit _ ≫ a.D₀.c χ} ∪
      {z | ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ q₀ : Out.QkPt a.D₀ F l.M,
        QkExt (algebraMap (FractionRing k) F) (a.eta v) q₀ ∧ z = q₀.g.b})


end ReciprocityTheory.ChartRestriction.G.Geo.Tor
