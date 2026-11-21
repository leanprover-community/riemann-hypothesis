import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwBack
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Imports
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import BuildAid.ForwardExisting
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistOkAll
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModuliIsReduced

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem twBack : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : HostAut H) (a : TwIso D g), ∃ a' : TwIso D g.symm, ∀ (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), (∀ (h : TwOK o g a) (h' : TwOK (twistObj o g a h) g.symm a'), Nonempty (ObjMap (twistObj (twistObj o g a h) g.symm a' h') o (𝟙 S))) ∧ ∀ (h : TwOK o g.symm a') (h' : TwOK (twistObj o g.symm a' h) g a), Nonempty (ObjMap (twistObj (twistObj o g.symm a' h) g a h') o (𝟙 S)) :=
  @PositivityTheory.UnitarySelfGeneration.tw_back

end GlobalTheory.CompanionTheory.Ar
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_inverse_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : HostAut H) (a : TwIso D g), ∃ a' : TwIso D g.symm, ∀ (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), (∀ (h : TwOK o g a) (h' : TwOK (twistObj o g a h) g.symm a'), Nonempty (ObjMap (twistObj (twistObj o g a h) g.symm a' h') o (𝟙 S))) ∧ ∀ (h : TwOK o g.symm a') (h' : TwOK (twistObj o g.symm a' h) g a), Nonempty (ObjMap (twistObj (twistObj o g.symm a' h) g a h') o (𝟙 S)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.twBack
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem tw_iso_nonempty : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : HostAut H), Nonempty (TwIso D g) :=
  PositivityTheory.UnitarySelfGeneration.tw_iso

end GlobalTheory.CompanionTheory.Ar
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_iso_nonempty : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : HostAut H), Nonempty (TwIso D g) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.tw_iso_nonempty
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem objMap_exists_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (S' S'' : Scheme.{0}) (s' : S' ⟶ Sp B) (s'' : S'' ⟶ Sp B) (o : Obj D l b s) (o' : Obj D l b s') (o'' : Obj D l b s'') (f : S' ⟶ S) (f' : S'' ⟶ S') (m : ObjMap o' o f) (m' : ObjMap o'' o' f'), ∃ n : ObjMap o'' o (f' ≫ f), n.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ := by
  intro E _ _ _ H D l B _ b S s S' S'' s' s'' o o' o'' f f' m m'
  obtain ⟨n, hn⟩ := sabComp pullCubComp E H S S' S'' o.t o'.t o''.t f f' m.toSABMap m'.toSABMap
  have hn' : n.cm.F = m'.cm.F ≫ m.cm.F := hn
  refine ⟨{ toSABMap := n, eta := fun x => ?_, etaA := fun x => ?_ }, hn⟩
  · rw [hn', ← Category.assoc, m'.eta, Category.assoc, m.eta, Category.assoc]
  · rw [hn', ← Category.assoc, m'.etaA, Category.assoc, m.etaA, Category.assoc]

end GlobalTheory.CompanionTheory.Ar
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.obj_map_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (S' S'' : Scheme.{0}) (s' : S' ⟶ Sp B) (s'' : S'' ⟶ Sp B) (o : Obj D l b s) (o' : Obj D l b s') (o'' : Obj D l b s'') (f : S' ⟶ S) (f' : S'' ⟶ S') (m : ObjMap o' o f) (m' : ObjMap o'' o' f'), ∃ n : ObjMap o'' o (f' ≫ f), n.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.objMap_exists_comp
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem objMap_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (S' : Scheme.{0}) (s' : S' ⟶ Sp B) (o : Obj D l b s) (o' : Obj D l b s') (f : S' ⟶ S) (m : ObjMap o' o f) (g : HostAut H) (a : TwIso D g) (h : TwOK o g a) (h' : TwOK o' g a), ∃ n : ObjMap (twistObj o' g a h') (twistObj o g a h) f, n.toSABMap = twistMap m.toSABMap g  := by
  intro E _ _ _ H D l B _ b S s S' s' o o' f m g a h h'
  exact ⟨{ toSABMap := twistMap m.toSABMap g
           eta := fun x => m.eta (a.a l.M x)
           etaA := fun x => m.etaA (a.a l.A x) }, rfl⟩

end GlobalTheory.CompanionTheory.Ar
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_obj_map_functorial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (S' : Scheme.{0}) (s' : S' ⟶ Sp B) (o : Obj D l b s) (o' : Obj D l b s') (f : S' ⟶ S) (m : ObjMap o' o f) (g : HostAut H) (a : TwIso D g) (h : TwOK o g a) (h' : TwOK o' g a), ∃ n : ObjMap (twistObj o' g a h') (twistObj o g a h) f, n.toSABMap = twistMap m.toSABMap g := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.objMap_twist
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem moduli_twist_phi : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (g : HostAut H) (a : TwIso D g) (h : TwOK Xo.univ g a),
    ∃ Φ : Xo.X ⟶ Xo.X, Φ ≫ Xo.s = Xo.s ∧ Nonempty (ObjMap (twistObj Xo.univ g a h) Xo.univ Φ) := by
  intro E _ _ _ H D l Xo g a h
  obtain ⟨f, ⟨hf, ho⟩, -⟩ :=
    Xo.rep Xo.X Xo.s (moduli_isReduced E H D l Xo) (twistObj Xo.univ g a h)
  exact ⟨f, hf, ho⟩

end GlobalTheory.CompanionTheory.Ar
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moduli_twist_automorphism : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (g : HostAut H) (a : TwIso D g) (h : TwOK Xo.univ g a), ∃ Φ : Xo.X ⟶ Xo.X, Φ ≫ Xo.s = Xo.s ∧ Nonempty (ObjMap (twistObj Xo.univ g a h) Xo.univ Φ) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.moduli_twist_phi
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isReduced_moduli' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l), IsReduced Xo.X := by
  first | exact @GlobalTheory.CompanionTheory.Ar.moduli_isReduced | exact GlobalTheory.CompanionTheory.Ar.moduli_isReduced | (intros; apply GlobalTheory.CompanionTheory.Ar.moduli_isReduced <;> assumption)
end

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TwistAutProof

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem eq_of_objMap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    (Xo : Moduli D l) {S : Scheme.{0}} (s' : S ⟶ Sp (KA l)) (hS : IsReduced S) (o : Obj D l (baseKA l) s')
    (f₁ f₂ : S ⟶ Xo.X) (h₁ : f₁ ≫ Xo.s = s') (h₂ : f₂ ≫ Xo.s = s') (m₁ : ObjMap o Xo.univ f₁)
    (m₂ : ObjMap o Xo.univ f₂) : f₁ = f₂ :=
  (Xo.rep S s' hS o).unique ⟨h₁, ⟨m₁⟩⟩ ⟨h₂, ⟨m₂⟩⟩

theorem twistAut : TwistAut := by
  intro E _ _ _ H D l Xo g
  refine ⟨GlobalTheory.T.twist_iso_nonempty E H D g, fun a => ?_⟩
  have hred : IsReduced Xo.X := GlobalTheory.T.isReduced_moduli' E H D l Xo
  obtain ⟨a', hback⟩ := GlobalTheory.T.twist_inverse_iso E H D g a
  have h : TwOK Xo.univ g a := GlobalTheory.T.twist_ok_all E H D l _ (baseKA l) Xo.X Xo.s Xo.univ g a
  have h' : TwOK Xo.univ g.symm a' := GlobalTheory.T.twist_ok_all E H D l _ (baseKA l) Xo.X Xo.s Xo.univ g.symm a'
  obtain ⟨Φ, hΦ, ⟨m⟩⟩ := GlobalTheory.T.moduli_twist_automorphism E H D l Xo g a h
  obtain ⟨Ψ, hΨ, ⟨m'⟩⟩ := GlobalTheory.T.moduli_twist_automorphism E H D l Xo g.symm a' h'
  obtain ⟨back₁, back₂⟩ := hback l _ (baseKA l) Xo.X Xo.s Xo.univ

  have e₁ : Φ ≫ Ψ = 𝟙 Xo.X := by
    have k : TwOK (twistObj Xo.univ g a h) g.symm a' :=
      GlobalTheory.T.twist_ok_all E H D l _ (baseKA l) Xo.X Xo.s _ g.symm a'
    obtain ⟨n, -⟩ := GlobalTheory.T.twist_obj_map_functorial E H D l _ (baseKA l) Xo.X Xo.s Xo.X Xo.s _ _ Φ m g.symm a' h' k
    obtain ⟨n', -⟩ := GlobalTheory.T.obj_map_comp E H D l _ (baseKA l) Xo.X Xo.s Xo.X Xo.X Xo.s Xo.s _ _ _ Ψ Φ m' n
    obtain ⟨i⟩ := back₁ h k
    exact eq_of_objMap Xo Xo.s hred _ _ _ (by rw [Category.assoc, hΨ, hΦ]) (Category.id_comp _) n' i

  have e₂ : Ψ ≫ Φ = 𝟙 Xo.X := by
    have k : TwOK (twistObj Xo.univ g.symm a' h') g a :=
      GlobalTheory.T.twist_ok_all E H D l _ (baseKA l) Xo.X Xo.s _ g a
    obtain ⟨n, -⟩ := GlobalTheory.T.twist_obj_map_functorial E H D l _ (baseKA l) Xo.X Xo.s Xo.X Xo.s _ _ Ψ m' g a h k
    obtain ⟨n', -⟩ := GlobalTheory.T.obj_map_comp E H D l _ (baseKA l) Xo.X Xo.s Xo.X Xo.X Xo.s Xo.s _ _ _ Φ Ψ m n
    obtain ⟨i⟩ := back₂ h' k
    exact eq_of_objMap Xo Xo.s hred _ _ _ (by rw [Category.assoc, hΦ, hΨ]) (Category.id_comp _) n' i
  exact ⟨h, ⟨Φ, Ψ, e₁, e₂⟩, hΦ, ⟨m⟩⟩

end GlobalTheory.CompanionTheory.Ar.TwistAutProof
end
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.TwistAut_holds : GlobalTheory.CompanionTheory.Ar.TwistAut := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.TwistAutProof.twistAut
end
