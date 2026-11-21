import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HTChartExists
import Development.WeilBound.CoreStatements.HodgeTatePoints.Weilfun
import Development.WeilBound.CoreStatements.HodgeTatePoints.Weilreg
import BuildAid.ForwardExisting

section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem weil_pairing_cubical : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S) (n : ℕ), 1 ≤ n → ∃ (w : ∀ (T : Over S) (x z : T ⟶ t.G), x ^ n = 1 → z ^ n = 1 → Γ(T.left, ⊤)ˣ), (∀ (T T' : Over S) (f : T' ⟶ T) (x z : T ⟶ t.G) (hx : x ^ n = 1) (hz : z ^ n = 1) (hx' : (f ≫ x) ^ n = 1) (hz' : (f ≫ z) ^ n = 1), (w T' (f ≫ x) (f ≫ z) hx' hz' : Γ(T'.left, ⊤)) = f.left.appTop.hom (w T x z hx hz)) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (g : Sp k ⟶ S), IsProper (Limits.pullback.snd t.G.hom g) → ∀ (x z : Over.mk g ⟶ t.G) (hx : x ^ n = 1) (hz : z ^ n = 1) (c : kˣ), Out.WeilIs t.G t.PP.L n x z (unitOn c) → w (Over.mk g) x z hx hz = unitOn c :=
  PositivityTheory.HtPt.Weilfun.weil_fun

end GlobalTheory.CompanionTheory.Ar.HT
end

section
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem weil_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S) (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsAlgClosed (FractionRing O)] (y : Sp O ⟶ S) (La : Type) [AddCommGroup La] (X : TorsTower p t.G y La) (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ), IsProper (Limits.pullback.snd t.G.hom ((BT.genPt O).hom ≫ y)) → (∀ n (a b : La) (ga gb : Over.mk ((BT.genPt O).hom ≫ y) ⟶ t.G), ga.left = ((X.Γ n).pt (lev p n a)).left ≫ X.i n → gb.left = ((X.Γ n).pt (lev p n b)).left ≫ X.i n → Out.WeilIs t.G t.PP.L ((p ^ n : ℕ) : ℤ) ga gb (unitOn (Units.map (algebraMap O (FractionRing O) : O →* FractionRing O) (ζ n ^ B a b)))) → X.PairingRegular B ζ :=
  PositivityTheory.HtPt.Weilreg.weil_regular_of_fun weil_pairing_cubical

end GlobalTheory.CompanionTheory.Ar.HT
end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_tower_weil_pairing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S) (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsAlgClosed (FractionRing O)] (y : Sp O ⟶ S) (La : Type) [AddCommGroup La] (X : TorsTower p t.G y La) (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ), IsProper (Limits.pullback.snd t.G.hom ((BT.genPt O).hom ≫ y)) → (∀ n (a b : La) (ga gb : Over.mk ((BT.genPt O).hom ≫ y) ⟶ t.G), ga.left = ((X.Γ n).pt (lev p n a)).left ≫ X.i n → gb.left = ((X.Γ n).pt (lev p n b)).left ≫ X.i n → Out.WeilIs t.G t.PP.L ((p ^ n : ℕ) : ℤ) ga gb (unitOn (Units.map (algebraMap O (FractionRing O) : O →* FractionRing O) (ζ n ^ B a b)))) → X.PairingRegular B ζ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.HT.weil_regular
end
